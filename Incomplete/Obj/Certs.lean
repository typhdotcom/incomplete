import Incomplete.Obj.Check
import Incomplete.Second

/-!
# The checker at symbolic certificates: `appDF`

`certT T R c` is the checker's verdict on the certificate number `c` (`0` when it checks) and
`jT c` its judgment's number. For symbolic child certificates `c₁ c₂` that check, with
judgments `Γ ⊢ f ≡ f' : ∀ A, B` and `Γ ⊢ a ≡ a' : A`, the `appDF` certificate
`appT g A B f f' a a' c₁ c₂` (its real number, `16 * ⟨…⟩ + 5`) checks (`certT_appT`), and its
judgment is `Γ ⊢ f a ≡ f' a' : B[a]` with `B[a]` the code `instT B a 0` (`jT_appT`).

`chkT T` at a sentence number `s` and a certificate `c` that checks, whose judgment is
`[] ⊢ e ≡ e : s`, is `0` (`chk_of_cert`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- The checker's verdict on the certificate number `c`: `0` when it checks. -/
noncomputable abbrev certT (T : Tables) (R : Nat → Bool) (c : VExpr) : VExpr := cov (certStep T R) c

/-- The number of the judgment of the certificate number `c`. -/
abbrev jT (c : VExpr) : VExpr := fldT 0 (div 16 c)

/-- `k * p + t`. -/
abbrev tagT (k t : Nat) (p : VExpr) : VExpr := add (mul (lit k) p) (lit t)

/-- The number of the judgment `Γ ⊢ a ≡ b : c` from those of its parts. -/
abbrev judgT (g a b c : VExpr) : VExpr := pair g (pair a (pair b c))

/-- The number of the `appDF` certificate from `c₁ : Γ ⊢ f ≡ f' : ∀ A, B` and
`c₂ : Γ ⊢ a ≡ a' : A`. -/
def appT (g A B f f' a a' c₁ c₂ : VExpr) : VExpr :=
  tagT 16 5 (pair (judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero))
    (pair A (pair B (pair f (pair f' (pair a (pair a' (pair c₁ c₂))))))))

@[obj_simp] theorem appT_liftN {g A B f f' a a' c₁ c₂ : VExpr} {n k : Nat} :
    (appT g A B f f' a a' c₁ c₂).liftN n k = appT (g.liftN n k) (A.liftN n k) (B.liftN n k)
      (f.liftN n k) (f'.liftN n k) (a.liftN n k) (a'.liftN n k) (c₁.liftN n k) (c₂.liftN n k) := by
  simp only [appT, obj_simp]

@[obj_simp] theorem appT_inst {g A B f f' a a' c₁ c₂ e : VExpr} {k : Nat} :
    (appT g A B f f' a a' c₁ c₂).inst e k = appT (g.inst e k) (A.inst e k) (B.inst e k)
      (f.inst e k) (f'.inst e k) (a.inst e k) (a'.inst e k) (c₁.inst e k) (c₂.inst e k) := by
  simp only [appT, obj_simp]

theorem appTTy {env : VEnv} [ObjEnv env] {Γ : List VExpr} {g A B f f' a a' c₁ c₂ : VExpr}
    (hg : Tm env Γ g) (hA : Tm env Γ A) (hB : Tm env Γ B) (hf : Tm env Γ f) (hf' : Tm env Γ f')
    (ha : Tm env Γ a) (ha' : Tm env Γ a') (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂) :
    Tm env Γ (appT g A B f f' a a' c₁ c₂) := by
  unfold appT; otype

macro_rules
  | `(tactic| otype_rules) => `(tactic| ((with_reducible refine appTTy ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) <;> otype))

/-- The code of the `appDF` certificate from codes of its parts. -/
def appC (g A B f f' a a' c₁ c₂ : PR) : PR :=
  tagC 16 5 (cpair (judgC g (tagC 7 3 (cpair f a)) (tagC 7 3 (cpair f' a')) (instP B a (num 0)))
    (cpair A (cpair B (cpair f (cpair f' (cpair a (cpair a' (cpair c₁ c₂))))))))

/-- `chkT T` at the sentence number `s` and the certificate number `c`: `0` when `c` proves the
sentence numbered `s`. -/
noncomputable abbrev prfT (T : Tables) (s c : VExpr) : VExpr := ev (chkT T) [s, c]

section
variable {env : VEnv} [E : ObjEnv env] {Γ l : List VExpr} {a b c d e g A B f f' a' c₁ c₂ x : VExpr}

/-! ### Codes of the rules at symbolic arguments -/

theorem ev_judgC {p q r s : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (judgC p q r s) l =ₒ judgT (ev p l) (ev q l) (ev r l) (ev s l)) := by
  simp only [judgC]; orw [ev_cpair hl, ev_cpair hl, ev_cpair hl]

theorem ev_childJC {p : PR} (hl : Tms env Γ l) : Thm env Γ (ev (childJC p) l =ₒ jT (ev p l)) := by
  simp only [childJC]; orw [ev_fldC hl, ev_divC hl, ← div_eq]

theorem ev_instP {p q r : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (instP p q r) l =ₒ instT (ev p l) (ev q l) (ev r l)) := by
  simp only [instP]; orw [ev_comp3 rfl hl]
  rw [ev_take3 bnd_instC]; orefl

theorem ev_histAt {p : PR} {n H : VExpr} (hn : Tm env Γ n) (hH : Tm env Γ H) :
    Thm env Γ (ev (histAt p) [n, H] =ₒ nth H (sub (sub n (lit 1)) (ev p [n, H]))) := by
  simp only [histAt]; orw [ev_nthC (by otype), ev_leq rfl (by otype), ev_leq rfl (by otype)]

theorem certT_eq {T : Tables} {R : Nat → Bool} (hc : Tm env Γ c) :
    Thm env Γ (certT T R c =ₒ ev (certStep T R) [c, hist (certStep T R) c]) :=
  cov_eq (bnd_certStep T R) hc

/-- A certificate below `n` is read off the history at `n`. -/
theorem histAt_cert {T : Tables} {R : Nat → Bool} {p : PR} {n : VExpr} (hn : Tm env Γ n)
    (hp : Thm env Γ (ev p [n, hist (certStep T R) n] =ₒ c)) (hc : Tm env Γ c)
    (h : Thm env Γ (c <ₒ n)) :
    Thm env Γ (ev (histAt p) [n, hist (certStep T R) n] =ₒ certT T R c) := by
  orw [ev_histAt hn (by otype), hp]
  exact nth_hist_lt (bnd_certStep T R) hc hn h

theorem ev_appC {g A B f f' a a' c₁ c₂ : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (appC g A B f f' a a' c₁ c₂) l =ₒ appT (ev g l) (ev A l) (ev B l) (ev f l)
      (ev f' l) (ev a l) (ev a' l) (ev c₁ l) (ev c₂ l)) := by
  simp only [appC, appT]
  orw [ev_tagC hl, ev_cpair hl, ev_judgC hl, ev_tagC hl, ev_tagC hl, ev_cpair hl, ev_cpair hl,
    ev_instP hl, ev_cpair hl, ev_cpair hl, ev_cpair hl, ev_cpair hl, ev_cpair hl, ev_cpair hl,
    ev_cpair hl]

/-! ### The conclusion -/

/-- A certificate of `[] ⊢ e ≡ e : s` that checks proves `s`. -/
theorem prfT_of_cert {T : Tables} {s : VExpr} (hs : Tm env Γ s) (hc : Tm env Γ c) (he : Tm env Γ e)
    (h : Thm env Γ (certT T (fun _ => true) c =ₒ zero)) (j : Thm env Γ (jT c =ₒ judgT zero e e s)) :
    Thm env Γ (prfT T s c =ₒ zero) := by
  have hl : Tms env Γ [s, c] := by otype
  have hJ : Thm env Γ (ev concC [s, c] =ₒ judgT zero e e s) := by
    simp only [concC]; orw [ev_fldC hl, ev_divC hl, ← div_eq, j]
  have hf : ∀ i, Thm env Γ (ev (fldC i concC) [s, c] =ₒ fldT i (judgT zero e e s)) := fun i => by
    orw [ev_fldC hl, hJ]
  simp only [prfT, chkT, chkC]
  refine ev_andz_zero rfl hl ?_ (ev_andz_zero rfl hl ?_ (ev_andz_zero rfl hl ?_ ?_))
  · orw [ev_push rfl hl]
    rw [ev_take 1 (bnd_certC T _)]
    exact h
  · refine ev_eqz_of_eq hl ?_
    orw [hf, fldT_pair_zero zeroTy (by otype)]
  · refine ev_eqz_of_eq hl ?_
    orw [hf, hf, fldT_pair_succ zeroTy (by otype), fldT_pair_zero he (by otype),
      fldT_pair_succ zeroTy (by otype), fldT_pair_succ he (by otype), fldT_pair_zero he hs]
  · refine ev_eqz_of_eq hl ?_
    orw [ev_restC hl, hJ, restT_pair_succ zeroTy (by otype), restT_pair_succ he (by otype),
      restT_pair_succ he hs]

/-! ### `appDF` -/

theorem tuple9 (h1 : Tm env Γ a) (h2 : Tm env Γ A) (h3 : Tm env Γ B) (h4 : Tm env Γ f)
    (h5 : Tm env Γ f') (h6 : Tm env Γ b) (h7 : Tm env Γ a') (h8 : Tm env Γ c₁) (h9 : Tm env Γ c₂)
    (hx : x = pair a (pair A (pair B (pair f (pair f' (pair b (pair a' (pair c₁ c₂)))))))) :
    Thm env Γ (fldT 0 x =ₒ a) ∧ Thm env Γ (fldT 1 x =ₒ A) ∧ Thm env Γ (fldT 2 x =ₒ B) ∧
    Thm env Γ (fldT 3 x =ₒ f) ∧ Thm env Γ (fldT 4 x =ₒ f') ∧ Thm env Γ (fldT 5 x =ₒ b) ∧
    Thm env Γ (fldT 6 x =ₒ a') ∧ Thm env Γ (fldT 7 x =ₒ c₁) ∧ Thm env Γ (restT 8 x =ₒ c₂) := by
  subst hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fldT_pair_zero h1 (by otype)
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_zero h2 (by otype)]
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_succ h2 (by otype), fldT_pair_zero h3 (by otype)]
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_succ h2 (by otype), fldT_pair_succ h3 (by otype),
      fldT_pair_zero h4 (by otype)]
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_succ h2 (by otype), fldT_pair_succ h3 (by otype),
      fldT_pair_succ h4 (by otype), fldT_pair_zero h5 (by otype)]
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_succ h2 (by otype), fldT_pair_succ h3 (by otype),
      fldT_pair_succ h4 (by otype), fldT_pair_succ h5 (by otype), fldT_pair_zero h6 (by otype)]
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_succ h2 (by otype), fldT_pair_succ h3 (by otype),
      fldT_pair_succ h4 (by otype), fldT_pair_succ h5 (by otype), fldT_pair_succ h6 (by otype),
      fldT_pair_zero h7 (by otype)]
  · orw [fldT_pair_succ h1 (by otype), fldT_pair_succ h2 (by otype), fldT_pair_succ h3 (by otype),
      fldT_pair_succ h4 (by otype), fldT_pair_succ h5 (by otype), fldT_pair_succ h6 (by otype),
      fldT_pair_succ h7 (by otype), fldT_pair_zero h8 h9]
  · orw [restT_pair_succ h1 (by otype), restT_pair_succ h2 (by otype), restT_pair_succ h3 (by otype),
      restT_pair_succ h4 (by otype), restT_pair_succ h5 (by otype), restT_pair_succ h6 (by otype),
      restT_pair_succ h7 (by otype), restT_pair_succ h8 h9]

variable (hg : Tm env Γ g) (hA : Tm env Γ A) (hB : Tm env Γ B) (hf : Tm env Γ f)
  (hf' : Tm env Γ f') (ha : Tm env Γ a) (ha' : Tm env Γ a') (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂)
include hg hA hB hf hf' ha ha' hc₁ hc₂

/-- The judgment of the `appDF` certificate: `Γ ⊢ f a ≡ f' a' : B[a]`. -/
theorem jT_appT : Thm env Γ (jT (appT g A B f f' a a' c₁ c₂) =ₒ
    judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero)) := by
  simp only [appT, jT]
  orw [div_tag (by decide) (by otype) (litTy 5) (lit_lt (by decide)), fldT_pair_zero (by otype) (by otype)]

/-- **`appDF` at symbolic certificates.** From `c₁ : Γ ⊢ f ≡ f' : ∀ A, B` and `c₂ : Γ ⊢ a ≡ a' : A`
that check, the `appDF` certificate checks. -/
theorem certT_appT {T : Tables} {R : Nat → Bool} (hR : R 5 = true)
    (h₁ : Thm env Γ (certT T R c₁ =ₒ zero)) (h₂ : Thm env Γ (certT T R c₂ =ₒ zero))
    (j₁ : Thm env Γ (jT c₁ =ₒ judgT g f f' (tagT 7 5 (pair A B))))
    (j₂ : Thm env Γ (jT c₂ =ₒ judgT g a a' A)) :
    Thm env Γ (certT T R (appT g A B f f' a a' c₁ c₂) =ₒ zero) := by
  have hJT : Tm env Γ (judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero)) := by
    otype
  generalize hx : pair (judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero))
    (pair A (pair B (pair f (pair f' (pair a (pair a' (pair c₁ c₂))))))) = x
  have hxT : Tm env Γ x := by subst hx; otype
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := tuple9 hJT hA hB hf hf' ha ha' hc₁ hc₂ hx.symm
  have happ : appT g A B f f' a a' c₁ c₂ = tagT 16 5 x := by rw [appT, hx]
  rw [happ]
  generalize hn : tagT 16 5 x = n
  have hnT : Tm env Γ n := by subst hn; otype
  generalize hH : hist (certStep T R) n = H
  have hHT : Tm env Γ H := by subst hH; otype
  have hl : Tms env Γ [n, H] := by otype
  -- the payload and the fields
  have hX : Thm env Γ (ev xC [n, H] =ₒ x) := by
    simp only [xC]; orw [ev_divC hl, ← div_eq]
    rw [← hn]
    exact div_tag (by decide) hxT (litTy 5) (lit_lt (by decide))
  have hF : ∀ i, Thm env Γ (ev (fldC i xC) [n, H] =ₒ fldT i x) := fun i => by
    orw [ev_fldC hl, hX]
  have hR8 : Thm env Γ (ev (restC 8 xC) [n, H] =ₒ restT 8 x) := by orw [ev_restC hl, hX]
  have hJ' : Thm env Γ (ev jC [n, H] =ₒ
      judgT g (tagT 7 3 (pair f a)) (tagT 7 3 (pair f' a')) (instT B a zero)) := by
    show Thm env Γ (ev (fldC 0 xC) [n, H] =ₒ _)
    orw [hF, x0]
  have hg' : Thm env Γ (ev (fldC 0 jC) [n, H] =ₒ g) := by
    orw [ev_fldC hl, hJ']; exact fldT_pair_zero hg (by otype)
  have hlt : ∀ y, Tm env Γ y → Thm env Γ (y ≤ₒ x) → Thm env Γ (y <ₒ n) := fun y hy h => by
    subst hn
    exact lt_of_le_of_lt hy hxT (by otype) h (lt_tag (t := lit 4) (by decide) hxT (litTy 4))
  have lt₁ : Thm env Γ (c₁ <ₒ n) := hlt _ hc₁ (by orw [← x7]; exact fldT_le 7 hxT)
  have lt₂ : Thm env Γ (c₂ <ₒ n) := hlt _ hc₂ (by orw [← x8]; exact restT_le 8 hxT)
  -- the step at a certificate with tag `5` runs `appDFC`
  orw [certT_eq hnT]
  rw [hH]
  have hstep := ev_certStep_tag (T := T) (R := R) (t := 5) (by decide) hxT hHT
  rw [hR, if_pos rfl, show add (mul (lit 16) x) (lit 5) = n from hn] at hstep
  orw [hstep]
  show Thm env Γ (ev appDFC [n, H] =ₒ zero)
  refine ev_andz_zero rfl hl ?_ (ev_andz_zero rfl hl ?_ (ev_andz_zero rfl hl ?_
    (ev_andz_zero rfl hl ?_ ?_)))
  · refine ev_eqz_of_eq hl ?_
    orw [hJ', ev_judgC hl, hg', ev_tagC hl, ev_tagC hl, ev_instP hl, ev_cpair hl, ev_cpair hl, hF, hF,
      hF, hF, hF, x2, x3, x4, x5, x6]
  · refine ev_eqz_of_eq hl ?_
    orw [ev_childJC hl, hF, x7, j₁, ev_judgC hl, hg', ev_tagC hl, ev_cpair hl, hF, hF, hF, hF, x1, x2,
      x3, x4]
  · refine ev_eqz_of_eq hl ?_
    orw [ev_childJC hl, hR8, x8, j₂, ev_judgC hl, hg', hF, hF, hF, x1, x5, x6]
  · rw [← hH]; orw [histAt_cert hnT (by rw [hH]; orw [hF, x7]) hc₁ lt₁, h₁]
  · rw [← hH]; orw [histAt_cert hnT (by rw [hH]; orw [hR8, x8]) hc₂ lt₂, h₂]
end

end Incomplete.Obj
