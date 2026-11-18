import Incomplete.Obj.Cov
import Incomplete.Obj.Reads

/-!
# The capped recursion over numbered expressions

`liftC` and `instC` recurse over an expression number `e` with a cutoff `k` by course-of-values
recursion with a parameter `p` on the capped key `keyT e k = pair e (min k (e + 1))`
(`capKey`); `kcov st p e k` is that recursion by the step `st`. Both steps read the key in
variable `1` as the expression `stE`, cutoff `stK`, tag `stT` and payload `stP`, and both are a
dispatch on the tag whose branches past the variable branch are the same (`stBranches`,
`stProj`). For such a step and symbolic components, one equation per constructor of `encExpr`
(`7 * p + t`): sorts and constants are kept, and `app`, `lam`, `forallE` and `proj` recurse into
their components, at `k + 1` under a binder. A component's key at the parent's cutoff is its own
key (`minT_minT`, `minT_succ_minT`) and lies below the parent's (`keyT_lt`), so its value is read
off the history (`kcov_child`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- `min a b`, as `minP` computes it: `a - (a - b)`. -/
abbrev minT (a b : VExpr) : VExpr := sub a (sub a b)

/-- The capped key `pair e (min k (e + 1))` of `capKey`. -/
abbrev keyT (e k : VExpr) : VExpr := pair e (minT k (S e))

/-- The recursion by `st` with the parameter `p`, at the expression `e` and cutoff `k`. -/
abbrev kcov (st : PR) (p e k : VExpr) : VExpr := covP st p (keyT e k)

/-! The parts of a step at the key in variable `1`: the expression, the cutoff, the tag and the
payload. -/
def stE : PR := fstC (var 1)
def stK : PR := sndC (var 1)
def stT : PR := modC 7 stE
def stP : PR := divC 7 stE

/-- The branches of a step for the tags `1` to `5`. -/
def stBranches : List PR := [stE, stE,
  tagC 7 3 (cpair (histK (fstC stP) stK) (histK (sndC stP) stK)),
  tagC 7 4 (cpair (histK (fstC stP) stK) (histK (sndC stP) (PR.succ stK))),
  tagC 7 5 (cpair (histK (fstC stP) stK) (histK (sndC stP) (PR.succ stK)))]

/-- The branch of a step for the tag `6`. -/
def stProj : PR := tagC 7 6 (cpair (fstC stP) (cpair (fstC (sndC stP)) (histK (sndC (sndC stP)) stK)))

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {a b c e f k k' n p t : VExpr}
  {st B0 : PR}

/-! ### `min` -/

theorem minT_of_le (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (minT a b =ₒ a) := by
  orw [h, sub_zero]

theorem minT_of_ge (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (b ≤ₒ a)) :
    Thm env Γ (minT a b =ₒ b) := by
  have e := le_elim hb ha h
  orw [← e, add_sub_cancel_left, add_sub_cancel]

theorem minT_le_left (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (minT a b ≤ₒ a) :=
  sub_le ha (by otype)

theorem minT_le_right (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (minT a b ≤ₒ b) := by
  ocases (le_total ha hb) with h1 h2
  · orw [minT_of_le (by otype) (by otype) h1]; exact h1
  · orw [minT_of_ge (by otype) (by otype) h2]; exact le_refl (by otype)

theorem le_minT (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) (h1 : Thm env Γ (c ≤ₒ a))
    (h2 : Thm env Γ (c ≤ₒ b)) : Thm env Γ (c ≤ₒ minT a b) := by
  ocases (le_total ha hb) with g1 g2
  · olift h1; orw [minT_of_le (by otype) (by otype) g1]; exact h1
  · olift h2; orw [minT_of_ge (by otype) (by otype) g2]; exact h2

theorem minT_minT (hk : Tm env Γ k) (he : Tm env Γ e) (hf : Tm env Γ f) (h : Thm env Γ (f ≤ₒ e)) :
    Thm env Γ (minT (minT k e) f =ₒ minT k f) := by
  ocases (le_total hk he) with g1 g2
  · orw [minT_of_le (by otype) (by otype) g1]
  · olift h
    orw [minT_of_ge (by otype) (by otype) g2]
    orw [minT_of_ge (by otype) (by otype) h,
      minT_of_ge (by otype) (by otype) (le_trans (by otype) (by otype) (by otype) h g2)]

theorem minT_succ_minT (hk : Tm env Γ k) (he : Tm env Γ e) (hf : Tm env Γ f)
    (h : Thm env Γ (f ≤ₒ S e)) : Thm env Γ (minT (S (minT k e)) f =ₒ minT (S k) f) := by
  ocases (le_total hk he) with g1 g2
  · orw [minT_of_le (by otype) (by otype) g1]
  · olift h
    orw [minT_of_ge (by otype) (by otype) g2]
    orw [minT_of_ge (by otype) (by otype) h, minT_of_ge (by otype) (by otype)
      (le_trans (by otype) (by otype) (by otype) h (succ_le_succ (by otype) (by otype) g2))]

/-! ### Keys -/

theorem ev_minP {a b : PR} (hl : Tms env Γ l) : Thm env Γ (ev (minP a b) l =ₒ minT (ev a l) (ev b l)) := by
  rw [minP]; orw [ev_leq rfl, ev_leq rfl]

theorem ev_keyC {a b : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (keyC a b) l =ₒ keyT (ev a l) (ev b l)) := by
  rw [keyC]; orw [ev_cpair, ev_minP]

theorem keyT_lt (hf : Tm env Γ f) (he : Tm env Γ e) (hk : Tm env Γ k) (hk' : Tm env Γ k')
    (h : Thm env Γ (S (S (add f f)) ≤ₒ e)) : Thm env Γ (keyT f k' <ₒ keyT e k) := by
  refine pair_lt_pair (by otype) (by otype) (by otype) (by otype) ?_
  have hX := minT_le_right (a := k') (b := S f) (by otype) (by otype)
  ole (add (add (sub (S f) (minT k' (S f))) (sub e (S (S (add f f))))) (minT k (S e))) [hX, h]

theorem ev_histK {a b : PR} {x y z : VExpr} (hx : Tm env Γ x) (hy : Tm env Γ y) (hz : Tm env Γ z) :
    Thm env Γ (ev (histK a b) [x, y, z] =ₒ
      nth z (sub (sub y (lit 1)) (keyT (ev a [x, y, z]) (ev b [x, y, z])))) := by
  rw [histK]; orw [ev_nthC, ev_leq rfl, ev_leq rfl, ev_keyC]

/-! ### The step at a key -/

variable {H : VExpr}

theorem rd_E (hn : Tm env Γ n) (he : Tm env Γ e) (hk : Tm env Γ k) (hH : Tm env Γ H) :
    Thm env Γ (ev stE [n, keyT e k, H] =ₒ e) := by
  rw [stE]; orw [ev_fstC, fst_pair]

theorem rd_K (hn : Tm env Γ n) (he : Tm env Γ e) (hk : Tm env Γ k) (hH : Tm env Γ H) :
    Thm env Γ (ev stK [n, keyT e k, H] =ₒ minT k (S e)) := by
  rw [stK]; orw [ev_sndC, snd_pair]

theorem rd_T {t : Nat} (ht : t < 7) (hn : Tm env Γ n) (hp : Tm env Γ p) (hk : Tm env Γ k)
    (hH : Tm env Γ H) :
    Thm env Γ (ev stT [n, keyT (add (mul (lit 7) p) (lit t)) k, H] =ₒ lit t) := by
  rw [stT]; orw [ev_modC, rd_E hn (by otype) hk hH, ← mod_eq]
  exact mod_tag (by omega) hp (litTy t) (lit_lt ht)

theorem rd_P {t : Nat} (ht : t < 7) (hn : Tm env Γ n) (hp : Tm env Γ p) (hk : Tm env Γ k)
    (hH : Tm env Γ H) :
    Thm env Γ (ev stP [n, keyT (add (mul (lit 7) p) (lit t)) k, H] =ₒ p) := by
  rw [stP]; orw [ev_divC, rd_E hn (by otype) hk hH, ← div_eq]
  exact div_tag (by omega) hp (litTy t) (lit_lt ht)

/-- A component of a tagged number's payload is well below it. -/
theorem child_bound {j : Nat} (hc : Tm env Γ c) (hp : Tm env Γ p) (h : Thm env Γ (c ≤ₒ p)) :
    Thm env Γ (S (S (add c c)) ≤ₒ add (mul (lit 7) p) (lit (j + 2))) := by
  ole (add (mul (lit 2) (sub p c)) (add (mul (lit 5) p) (lit j))) [h]

theorem ev_st_casc (hst : st = ifz stT B0 (casc stT stBranches stProj 1)) (hl : Tms env Γ l) :
    Thm env Γ (ev st l =ₒ ev (ifz stT B0 (casc stT stBranches stProj 1)) l) := by
  subst hst; exact Thm.refl (evTy hl)

/-- A component's value, read off the history at the parent's key. -/
theorem kcov_child (hb : bnd st ≤ 3) (hp : Tm env Γ p) (he : Tm env Γ e) (hk : Tm env Γ k)
    (hc : Tm env Γ c) (h : Thm env Γ (S (S (add c c)) ≤ₒ e)) :
    Thm env Γ (nth (histP st p (keyT e k)) (sub (sub (keyT e k) (lit 1))
      (keyT c (minT k (S e)))) =ₒ kcov st p c k) := by
  have hce : Thm env Γ (S c ≤ₒ S e) := by ole (add (S (S c)) (sub e (S (S (add c c))))) [h]
  have e1 : Thm env Γ (keyT c (minT k (S e)) =ₒ keyT c k) := by
    simp only [keyT]; orw [minT_minT hk (STy he) (STy hc) hce]
  orw [e1, nth_histP_lt hb hp (by otype) (by otype) (keyT_lt (k' := k) hc he hk hk h)]

/-- A component under a binder: the cutoff grows by one. -/
theorem kcov_child_succ (hb : bnd st ≤ 3) (hp : Tm env Γ p) (he : Tm env Γ e) (hk : Tm env Γ k)
    (hc : Tm env Γ c) (h : Thm env Γ (S (S (add c c)) ≤ₒ e)) :
    Thm env Γ (nth (histP st p (keyT e k)) (sub (sub (keyT e k) (lit 1))
      (keyT c (S (minT k (S e))))) =ₒ kcov st p c (S k)) := by
  have hce : Thm env Γ (S c ≤ₒ S (S e)) := by ole (add (S (S (S c))) (sub e (S (S (add c c))))) [h]
  have e1 : Thm env Γ (keyT c (S (minT k (S e))) =ₒ keyT c (S k)) := by
    simp only [keyT]; orw [minT_succ_minT hk (STy he) (STy hc) hce]
  orw [e1, nth_histP_lt hb hp (by otype) (by otype) (keyT_lt (k' := S k) hc he hk (by otype) h)]

/-! ### One equation per constructor -/

variable (hst : st = ifz stT B0 (casc stT stBranches stProj 1)) (hb : bnd st ≤ 3)
include hst hb

theorem kcov_app (hp : Tm env Γ p) (hf : Tm env Γ f) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (add (mul (lit 7) (pair f a)) (lit 3)) k =ₒ
      add (mul (lit 7) (pair (kcov st p f k) (kcov st p a k))) (lit 3)) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 2) (rd_T (t := 3) (by decide) hp (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 2 (by simp [stBranches])
    (rd_T (t := 3) (by decide) hp (by otype) hk (by otype))]
  simp only [stBranches, List.getElem_cons_succ, List.getElem_cons_zero]
  orw [ev_tagC, ev_cpair, ev_histK, ev_histK, ev_fstC, ev_sndC,
    rd_P (t := 3) (by decide) hp (by otype) hk (by otype),
    rd_K hp (by otype) hk (by otype), fst_pair hf ha, snd_pair hf ha]
  orw [kcov_child hb hp (by otype) hk hf (child_bound (j := 1) hf (by otype) (le_pair_left hf ha)),
    kcov_child hb hp (by otype) hk ha (child_bound (j := 1) ha (by otype) (le_pair_right hf ha))]

theorem kcov_lam (hp : Tm env Γ p) (ha : Tm env Γ a) (hb' : Tm env Γ b) (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (add (mul (lit 7) (pair a b)) (lit 4)) k =ₒ
      add (mul (lit 7) (pair (kcov st p a k) (kcov st p b (S k)))) (lit 4)) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 3) (rd_T (t := 4) (by decide) hp (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 3 (by simp [stBranches])
    (rd_T (t := 4) (by decide) hp (by otype) hk (by otype))]
  simp only [stBranches, List.getElem_cons_succ, List.getElem_cons_zero]
  orw [ev_tagC, ev_cpair, ev_histK, ev_histK, ev_fstC, ev_sndC,
    rd_P (t := 4) (by decide) hp (by otype) hk (by otype),
    rd_K hp (by otype) hk (by otype), fst_pair ha hb', snd_pair ha hb']
  orw [kcov_child hb hp (by otype) hk ha (child_bound (j := 2) ha (by otype) (le_pair_left ha hb')),
    kcov_child_succ hb hp (by otype) hk hb' (child_bound (j := 2) hb' (by otype) (le_pair_right ha hb'))]

theorem kcov_forallE (hp : Tm env Γ p) (ha : Tm env Γ a) (hb' : Tm env Γ b) (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (add (mul (lit 7) (pair a b)) (lit 5)) k =ₒ
      add (mul (lit 7) (pair (kcov st p a k) (kcov st p b (S k)))) (lit 5)) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 4) (rd_T (t := 5) (by decide) hp (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 4 (by simp [stBranches])
    (rd_T (t := 5) (by decide) hp (by otype) hk (by otype))]
  simp only [stBranches, List.getElem_cons_succ, List.getElem_cons_zero]
  orw [ev_tagC, ev_cpair, ev_histK, ev_histK, ev_fstC, ev_sndC,
    rd_P (t := 5) (by decide) hp (by otype) hk (by otype),
    rd_K hp (by otype) hk (by otype), fst_pair ha hb', snd_pair ha hb']
  orw [kcov_child hb hp (by otype) hk ha (child_bound (j := 3) ha (by otype) (le_pair_left ha hb')),
    kcov_child_succ hb hp (by otype) hk hb' (child_bound (j := 3) hb' (by otype) (le_pair_right ha hb'))]

theorem kcov_proj (hp : Tm env Γ p) (hs : Tm env Γ a) (hi : Tm env Γ b) (he : Tm env Γ e)
    (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (add (mul (lit 7) (pair a (pair b e))) (lit 6)) k =ₒ
      add (mul (lit 7) (pair a (pair b (kcov st p e k)))) (lit 6)) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 5) (rd_T (t := 6) (by decide) hp (by otype) hk (by otype))]
  orw [ev_casc_end (by otype) _ 1 5 (by simp [stBranches])
    (rd_T (t := 6) (by decide) hp (by otype) hk (by otype))]
  rw [stProj]
  orw [ev_tagC, ev_cpair, ev_cpair, ev_histK, ev_fstC, ev_fstC, ev_sndC, ev_sndC,
    rd_P (t := 6) (by decide) hp (by otype) hk (by otype),
    rd_K hp (by otype) hk (by otype), fst_pair hs (by otype), snd_pair hs (by otype),
    fst_pair hi he, snd_pair hi he]
  have hb'' : Thm env Γ (e ≤ₒ pair a (pair b e)) :=
    le_trans he (by otype) (by otype) (le_pair_right hi he) (le_pair_right hs (by otype))
  orw [kcov_child hb hp (by otype) hk he (child_bound (j := 4) he (by otype) hb'')]

theorem kcov_sort (hp : Tm env Γ p) (hu : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (add (mul (lit 7) a) (lit 1)) k =ₒ add (mul (lit 7) a) (lit 1)) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_succ rfl (by otype) zeroTy (rd_T (t := 1) (by decide) hp (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 0 (by simp [stBranches])
    (rd_T (t := 1) (by decide) hp (by otype) hk (by otype))]
  simp only [stBranches, List.getElem_cons_zero]
  orw [rd_E hp (by otype) hk (by otype)]

theorem kcov_const (hp : Tm env Γ p) (hc : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (add (mul (lit 7) a) (lit 2)) k =ₒ add (mul (lit 7) a) (lit 2)) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 1) (rd_T (t := 2) (by decide) hp (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 1 (by simp [stBranches])
    (rd_T (t := 2) (by decide) hp (by otype) hk (by otype))]
  simp only [stBranches, List.getElem_cons_succ, List.getElem_cons_zero]
  orw [rd_E hp (by otype) hk (by otype)]

omit hst hb in
theorem rd_T0 (hn : Tm env Γ n) (hp : Tm env Γ p) (hk : Tm env Γ k) (hH : Tm env Γ H) :
    Thm env Γ (ev stT [n, keyT (mul (lit 7) p) k, H] =ₒ zero) := by
  have h := rd_T (t := 0) (by decide) hn hp hk hH
  simp only [lit_zero] at h
  orw [add_zero] at h; exact h

omit hst hb in
theorem rd_P0 (hn : Tm env Γ n) (hp : Tm env Γ p) (hk : Tm env Γ k) (hH : Tm env Γ H) :
    Thm env Γ (ev stP [n, keyT (mul (lit 7) p) k, H] =ₒ p) := by
  have h := rd_P (t := 0) (by decide) hn hp hk hH
  simp only [lit_zero] at h
  orw [add_zero] at h; exact h

/-- A variable: the step's own branch. -/
theorem kcov_bvar (hp : Tm env Γ p) (hi : Tm env Γ n) (hk : Tm env Γ k) :
    Thm env Γ (kcov st p (mul (lit 7) n) k =ₒ
      ev B0 [p, keyT (mul (lit 7) n) k, histP st p (keyT (mul (lit 7) n) k)]) := by
  orw [covP_eq hb hp (by otype), ev_st_casc hst (by otype)]
  orw [ev_ifz_zero rfl (by otype) (rd_T0 hp hi hk (by otype))]

end
end Incomplete.Obj
