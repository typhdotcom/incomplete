import Incomplete.Obj.Cov
import Incomplete.Obj.Reads

/-!
# Lifting numbered expressions, one constructor at a time

`liftT n e k` is the code `liftC` at `[n, e, k]`, the number of `(decExpr e).liftN n k`. For each
constructor of `encExpr` (`7 * i` for a variable, `7 * p + t` otherwise) at symbolic components,
the equation that one step of the recursion gives: a variable below the cutoff `k` is kept, one at
or above it is moved up by `n` (`liftT_bvar_lt`, `liftT_bvar_ge`); sorts and constants are kept;
`app`, `lam`, `forallE` and `proj` lift their components, at `k + 1` under a binder. The recursion
runs on the capped key `keyT e k = pair e (min k (e + 1))`; a component's key at the parent's
cutoff is its own key (`minT_minT`, `minT_succ_minT`) and lies below the parent's (`keyT_lt`), so
it is read off the history (`lift_child`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- `min a b`, as `minP` computes it: `a - (a - b)`. -/
abbrev minT (a b : VExpr) : VExpr := sub a (sub a b)

/-- The capped key `pair e (min k (e + 1))` of `capKey`. -/
abbrev keyT (e k : VExpr) : VExpr := pair e (minT k (S e))

/-- `liftNum n e k`: the code `liftC` at `[n, e, k]`. -/
abbrev liftT (n e k : VExpr) : VExpr := ev liftC [n, e, k]

theorem bnd_liftStep : bnd liftStep ≤ 3 := by unfold liftStep; obnd
theorem bnd_covPC_liftStep : bnd (covPC liftStep) ≤ 2 := by have := bnd_liftStep; obnd

/-! The parts of a step at the key in variable `1`: the expression, the cutoff, the tag and the
payload. -/
def stE : PR := fstC (var 1)
def stK : PR := sndC (var 1)
def stT : PR := modC 7 stE
def stP : PR := divC 7 stE

/-- `liftStep` as a dispatch on the tag. -/
theorem liftStep_casc : liftStep =
    ifz stT (tagC 7 0 (ifz (leq (PR.succ stP) stK) stP (addP (var 0) stP)))
      (casc stT [stE, stE,
        tagC 7 3 (cpair (histK (fstC stP) stK) (histK (sndC stP) stK)),
        tagC 7 4 (cpair (histK (fstC stP) stK) (histK (sndC stP) (PR.succ stK))),
        tagC 7 5 (cpair (histK (fstC stP) stK) (histK (sndC stP) (PR.succ stK)))]
        (tagC 7 6 (cpair (fstC stP) (cpair (fstC (sndC stP)) (histK (sndC (sndC stP)) stK)))) 1) :=
  rfl

section
variable {env : VEnv} [E : ObjEnv env] {Γ l : List VExpr} {a b c e f k k' n p t : VExpr}

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

theorem liftT_eq (hn : Tm env Γ n) (he : Tm env Γ e) (hk : Tm env Γ k) :
    Thm env Γ (liftT n e k =ₒ covP liftStep n (keyT e k)) := by

  orw [ev_comp2 (f := liftC) rfl]
  rw [ev_take2 bnd_covPC_liftStep _ _ (_ :: _)]
  orw [ev_keyC]

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

theorem ev_liftStep_casc (hl : Tms env Γ l) : Thm env Γ (ev liftStep l =ₒ
    ev (ifz stT (tagC 7 0 (ifz (leq (PR.succ stP) stK) stP (addP (var 0) stP)))
      (casc stT [stE, stE,
        tagC 7 3 (cpair (histK (fstC stP) stK) (histK (sndC stP) stK)),
        tagC 7 4 (cpair (histK (fstC stP) stK) (histK (sndC stP) (PR.succ stK))),
        tagC 7 5 (cpair (histK (fstC stP) stK) (histK (sndC stP) (PR.succ stK)))]
        (tagC 7 6 (cpair (fstC stP) (cpair (fstC (sndC stP)) (histK (sndC (sndC stP)) stK)))) 1)) l) :=
  (Thm.refl (evTy hl)).cast (by rw [← liftStep_casc])

/-- A child's lift, read off the history at the parent's key. -/
theorem lift_child (hn : Tm env Γ n) (he : Tm env Γ e) (hk : Tm env Γ k) (hc : Tm env Γ c)
    (h : Thm env Γ (S (S (add c c)) ≤ₒ e)) :
    Thm env Γ (nth (histP liftStep n (keyT e k)) (sub (sub (keyT e k) (lit 1))
      (keyT c (minT k (S e)))) =ₒ liftT n c k) := by
  have hce : Thm env Γ (S c ≤ₒ S e) := by ole (add (S (S c)) (sub e (S (S (add c c))))) [h]
  have e1 : Thm env Γ (keyT c (minT k (S e)) =ₒ keyT c k) := by
    simp only [keyT]; orw [minT_minT hk (STy he) (STy hc) hce]
  orw [e1, nth_histP_lt bnd_liftStep hn (by otype) (by otype) (keyT_lt (k' := k) hc he hk hk h),
    ← liftT_eq hn hc hk]

/-- A child under a binder: the cutoff grows by one. -/
theorem lift_child_succ (hn : Tm env Γ n) (he : Tm env Γ e) (hk : Tm env Γ k) (hc : Tm env Γ c)
    (h : Thm env Γ (S (S (add c c)) ≤ₒ e)) :
    Thm env Γ (nth (histP liftStep n (keyT e k)) (sub (sub (keyT e k) (lit 1))
      (keyT c (S (minT k (S e))))) =ₒ liftT n c (S k)) := by
  have hce : Thm env Γ (S c ≤ₒ S (S e)) := by ole (add (S (S (S c))) (sub e (S (S (add c c))))) [h]
  have e1 : Thm env Γ (keyT c (S (minT k (S e))) =ₒ keyT c (S k)) := by
    simp only [keyT]; orw [minT_succ_minT hk (STy he) (STy hc) hce]
  orw [e1, nth_histP_lt bnd_liftStep hn (by otype) (by otype)
      (keyT_lt (k' := S k) hc he hk (by otype) h), ← liftT_eq hn hc (STy hk)]

/-! ### One equation per constructor -/

theorem liftT_app (hn : Tm env Γ n) (hf : Tm env Γ f) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair f a)) (lit 3)) k =ₒ
      add (mul (lit 7) (pair (liftT n f k) (liftT n a k))) (lit 3)) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 2) (rd_T (t := 3) (by decide) hn (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 2 (by simp) (rd_T (t := 3) (by decide) hn (by otype) hk (by otype))]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  orw [ev_tagC, ev_cpair, ev_histK, ev_histK, ev_fstC, ev_sndC,
    rd_P (t := 3) (by decide) hn (by otype) hk (by otype),
    rd_K hn (by otype) hk (by otype), fst_pair hf ha, snd_pair hf ha]
  orw [lift_child hn (by otype) hk hf (child_bound (j := 1) hf (by otype) (le_pair_left hf ha)),
    lift_child hn (by otype) hk ha (child_bound (j := 1) ha (by otype) (le_pair_right hf ha))]

theorem liftT_lam (hn : Tm env Γ n) (ha : Tm env Γ a) (hb : Tm env Γ b) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair a b)) (lit 4)) k =ₒ
      add (mul (lit 7) (pair (liftT n a k) (liftT n b (S k)))) (lit 4)) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 3) (rd_T (t := 4) (by decide) hn (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 3 (by simp) (rd_T (t := 4) (by decide) hn (by otype) hk (by otype))]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  orw [ev_tagC, ev_cpair, ev_histK, ev_histK, ev_fstC, ev_sndC,
    rd_P (t := 4) (by decide) hn (by otype) hk (by otype),
    rd_K hn (by otype) hk (by otype), fst_pair ha hb, snd_pair ha hb]
  orw [lift_child hn (by otype) hk ha (child_bound (j := 2) ha (by otype) (le_pair_left ha hb)),
    lift_child_succ hn (by otype) hk hb (child_bound (j := 2) hb (by otype) (le_pair_right ha hb))]

theorem liftT_forallE (hn : Tm env Γ n) (ha : Tm env Γ a) (hb : Tm env Γ b) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair a b)) (lit 5)) k =ₒ
      add (mul (lit 7) (pair (liftT n a k) (liftT n b (S k)))) (lit 5)) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 4) (rd_T (t := 5) (by decide) hn (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 4 (by simp) (rd_T (t := 5) (by decide) hn (by otype) hk (by otype))]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  orw [ev_tagC, ev_cpair, ev_histK, ev_histK, ev_fstC, ev_sndC,
    rd_P (t := 5) (by decide) hn (by otype) hk (by otype),
    rd_K hn (by otype) hk (by otype), fst_pair ha hb, snd_pair ha hb]
  orw [lift_child hn (by otype) hk ha (child_bound (j := 3) ha (by otype) (le_pair_left ha hb)),
    lift_child_succ hn (by otype) hk hb (child_bound (j := 3) hb (by otype) (le_pair_right ha hb))]

theorem liftT_proj (hn : Tm env Γ n) (hs : Tm env Γ a) (hi : Tm env Γ b) (he : Tm env Γ e)
    (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) (pair a (pair b e))) (lit 6)) k =ₒ
      add (mul (lit 7) (pair a (pair b (liftT n e k)))) (lit 6)) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 5) (rd_T (t := 6) (by decide) hn (by otype) hk (by otype))]
  orw [ev_casc_end (by otype) _ 1 5 (by simp) (rd_T (t := 6) (by decide) hn (by otype) hk (by otype))]
  orw [ev_tagC, ev_cpair, ev_cpair, ev_histK, ev_fstC, ev_fstC, ev_sndC, ev_sndC,
    rd_P (t := 6) (by decide) hn (by otype) hk (by otype),
    rd_K hn (by otype) hk (by otype), fst_pair hs (by otype), snd_pair hs (by otype),
    fst_pair hi he, snd_pair hi he]
  have hb : Thm env Γ (e ≤ₒ pair a (pair b e)) :=
    le_trans he (by otype) (by otype) (le_pair_right hi he) (le_pair_right hs (by otype))
  orw [lift_child hn (by otype) hk he (child_bound (j := 4) he (by otype) hb)]

theorem liftT_sort (hn : Tm env Γ n) (hu : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) a) (lit 1)) k =ₒ add (mul (lit 7) a) (lit 1)) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_succ rfl (by otype) zeroTy (rd_T (t := 1) (by decide) hn (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 0 (by simp) (rd_T (t := 1) (by decide) hn (by otype) hk (by otype))]
  simp only [List.getElem_cons_zero]
  orw [rd_E hn (by otype) hk (by otype)]

theorem liftT_const (hn : Tm env Γ n) (hc : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (add (mul (lit 7) a) (lit 2)) k =ₒ add (mul (lit 7) a) (lit 2)) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_succ rfl (by otype) (litTy 1) (rd_T (t := 2) (by decide) hn (by otype) hk (by otype))]
  orw [ev_casc (by otype) _ 1 1 (by simp) (rd_T (t := 2) (by decide) hn (by otype) hk (by otype))]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  orw [rd_E hn (by otype) hk (by otype)]

theorem rd_T0 (hn : Tm env Γ n) (hp : Tm env Γ p) (hk : Tm env Γ k) (hH : Tm env Γ H) :
    Thm env Γ (ev stT [n, keyT (mul (lit 7) p) k, H] =ₒ zero) := by
  have h := rd_T (t := 0) (by decide) hn hp hk hH
  simp only [lit_zero] at h
  orw [add_zero] at h; exact h

theorem rd_P0 (hn : Tm env Γ n) (hp : Tm env Γ p) (hk : Tm env Γ k) (hH : Tm env Γ H) :
    Thm env Γ (ev stP [n, keyT (mul (lit 7) p) k, H] =ₒ p) := by
  have h := rd_P (t := 0) (by decide) hn hp hk hH
  simp only [lit_zero] at h
  orw [add_zero] at h; exact h

/-- The variable branch: the test of `i` against the cutoff, and the code's two outcomes. -/
theorem liftT_bvar_eq (hn : Tm env Γ n) (hi : Tm env Γ p) (hk : Tm env Γ k) :
    Thm env Γ (liftT n (mul (lit 7) p) k =ₒ add (mul (lit 7) (ev (ifz (leq (PR.succ stP) stK) stP
      (addP (var 0) stP)) [n, keyT (mul (lit 7) p) k, histP liftStep n (keyT (mul (lit 7) p) k)]))
      zero) := by
  orw [liftT_eq hn (by otype) hk, covP_eq bnd_liftStep hn (by otype), ev_liftStep_casc (by otype)]
  orw [ev_ifz_zero rfl (by otype) (rd_T0 hn hi hk (by otype)), ev_tagC]

theorem liftT_bvar_lt (hn : Tm env Γ n) (hi : Tm env Γ p) (hk : Tm env Γ k)
    (h : Thm env Γ (p <ₒ k)) : Thm env Γ (liftT n (mul (lit 7) p) k =ₒ mul (lit 7) p) := by
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [n, keyT (mul (lit 7) p) k, histP liftStep n (keyT (mul (lit 7) p) k)] =ₒ zero) := by
    orw [ev_leq rfl, rd_P0 hn hi hk (by otype), rd_K hn (by otype) hk (by otype)]
    refine le_minT hk (by otype) (by otype) h (succ_le_succ hi (by otype) ?_)
    have := le_tag (t := zero) hi zeroTy (by decide : 0 < 7)
    orw [add_zero] at this; exact this
  orw [liftT_bvar_eq hn hi hk, ev_ifz_zero rfl (by otype) hc, rd_P0 hn hi hk (by otype), add_zero]

theorem liftT_bvar_ge (hn : Tm env Γ n) (hi : Tm env Γ p) (hk : Tm env Γ k)
    (h : Thm env Γ (k ≤ₒ p)) : Thm env Γ (liftT n (mul (lit 7) p) k =ₒ mul (lit 7) (add n p)) := by
  have hK : Thm env Γ (minT k (S (mul (lit 7) p)) ≤ₒ p) :=
    le_trans (by otype) hk hi (minT_le_left hk (by otype)) h
  have hc : Thm env Γ (ev (leq (PR.succ stP) stK)
      [n, keyT (mul (lit 7) p) k, histP liftStep n (keyT (mul (lit 7) p) k)] =ₒ
      S (sub (S p) (S (minT k (S (mul (lit 7) p)))))) := by
    orw [ev_leq rfl, rd_P0 hn hi hk (by otype), rd_K hn (by otype) hk (by otype)]
    exact sub_eq_succ_of_lt (by otype) (by otype) (lt_succ_of_le (by otype) hi hK)
  orw [liftT_bvar_eq hn hi hk, ev_ifz_succ rfl (by otype) (by otype) hc]
  rw [addP]
  orw [ev_comp2, ev_fn2 (f := addC), rd_P0 hn hi hk (by otype), add_zero, add_comm (a := p)]

end
end Incomplete.Obj
