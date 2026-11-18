import Incomplete.Obj.Free

/-!
# Certificates at symbolic numerals

`numCertC z s` is the code of a certificate of `⊢ lit k : Nat` at `k`, by `appDF` from the
closed certificates `z` of `⊢ Nat.zero : Nat` and `s` of `⊢ Nat.succ : Nat → Nat`; the object
theory proves, by induction on `k`, that it checks and certifies `litT k : Nat`
(`numCert_c`). From a closed certificate of `∀ x : Nat, Q`, `appDF` at `numCert k` gives a
certificate of `Q[lit k]` for every `k`, the sentence number being `instT ⌜Q⌝ (litT k) 0`:
internally, `∀ k, Prf(⌜Q⌝[k], σ k)` for a code `σ` (`inst_c`, `internal_inst`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- The certificate of `⊢ lit k : Nat` at `k`, from `z : ⊢ Nat.zero : Nat` and
`s : ⊢ Nat.succ : Nat → Nat`. -/
def numCertC (z s : Nat) : PR :=
  prec (numC z) (appC (num 0) (numC (encExpr nat)) (numC (encExpr nat)) (numC (encExpr succ))
    (numC (encExpr succ)) (push (var 1) litC) (push (var 1) litC) (numC s) (var 0))

/-- `numCertC z s` at `k`. -/
abbrev numCert (z s : Nat) (k : VExpr) : VExpr := ev (numCertC z s) [k]

theorem bnd_litC : bnd litC ≤ 1 := by unfold litC; obnd

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {z s : Nat} {a k : VExpr}

theorem numCert_zero : Thm env Γ (numCert z s zero =ₒ numT z) := by
  orw [ev_prec_zero (f := numCertC z s) rfl (by otype)]

theorem numCert_succ (hk : Tm env Γ k) : Thm env Γ (numCert z s (S k) =ₒ
    appT zero (numT (encExpr nat)) (numT (encExpr nat)) (numT (encExpr succ)) (numT (encExpr succ))
      (litT k) (litT k) (numT s) (numCert z s k)) := by
  orw [ev_prec_succ (f := numCertC z s) rfl (by otype) hk]
  orw [ev_appC (by otype)]
  orw [ev_push rfl (by otype)]
  rw [ev_take 1 bnd_litC]
  simp only [ev_numC_ctx, List.take_succ_cons, List.take_zero]
  orefl

theorem instT_const_numT (c : Lean.Name) (ls : List VLevel) (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (numT (encExpr (.const c ls))) a k =ₒ numT (encExpr (.const c ls))) := by
  orw [numT_const, instT_const (by otype) ha hk]

theorem instT_numT_nat (ha : Tm env Γ a) (hk : Tm env Γ k) :
    Thm env Γ (instT (numT (encExpr nat)) a k =ₒ numT (encExpr nat)) := instT_const_numT _ _ ha hk

theorem numT_all (Q : VExpr) : Thm env Γ (numT (encExpr (all Q)) =ₒ
    tagT 7 5 (pair (numT (encExpr nat)) (numT (encExpr Q)))) := numT_forallE nat Q

variable {T : Tables}
  (hz : Thm env [] (certT T (fun _ => true) (numT z) =ₒ zero))
  (jz : Thm env [] (jT (numT z) =ₒ
    judgT zero (numT (encExpr Incomplete.zero)) (numT (encExpr Incomplete.zero)) (numT (encExpr nat))))
  (hs : Thm env [] (certT T (fun _ => true) (numT s) =ₒ zero))
  (js : Thm env [] (jT (numT s) =ₒ
    judgT zero (numT (encExpr succ)) (numT (encExpr succ)) (numT (encExpr (.forallE nat nat)))))
include hz jz hs js

/-- **Numerals are typed, internally.** For every `k`, `numCert k` checks and certifies
`⊢ lit k : Nat`. -/
theorem numCert_c : Thm env [] (∀ₒ k, certT T (fun _ => true) (numCert z s k) =ₒ zero ∧ₒ
    jT (numCert z s k) =ₒ judgT zero (litT k) (litT k) (numT (encExpr nat))) := by
  have js' : ∀ {Γ}, Thm env Γ (jT (numT s) =ₒ judgT zero (numT (encExpr succ)) (numT (encExpr succ))
      (tagT 7 5 (pair (numT (encExpr nat)) (numT (encExpr nat))))) := by
    intro Γ; orw [js.weak0, numT_forallE]
  oind
  · osplit
    · orw [numCert_zero]; exact hz.weak0
    · orw [numCert_zero, jz.weak0, litT_zero]
  · ointro ih
    ocases ih with h1 h2
    osplit
    · orw [numCert_succ (by otype)]
      exact certT_appT (by otype) (by otype) (by otype) (by otype) (by otype) (by otype) (by otype)
        (by otype) (by otype) rfl hs.weak0 h1 js' h2
    · orw [numCert_succ (by otype), jT_appT (by otype) (by otype) (by otype) (by otype) (by otype)
        (by otype) (by otype) (by otype) (by otype), instT_numT_nat (by otype) zeroTy,
        litT_succ (by otype)]

/-- The certificate of `Q[lit k]` at `k`, from the closed certificate `c` of `⊢ e : ∀ x : Nat, Q`. -/
def instCertC (z s : Nat) (Q e : VExpr) (c : Nat) : PR :=
  appC (num 0) (numC (encExpr nat)) (numC (encExpr Q)) (numC (encExpr e)) (numC (encExpr e)) litC
    litC (numC c) (numCertC z s)

/-- **Internal instantiation.** From a closed certificate of `⊢ e : ∀ x : Nat, Q`, for every `k`
the certificate `instCertC … k` proves the sentence numbered `instT ⌜Q⌝ (litT k) 0`. -/
theorem inst_c {Q e : VExpr} {c : Nat} (hc : Thm env [] (certT T (fun _ => true) (numT c) =ₒ zero))
    (jc : Thm env [] (jT (numT c) =ₒ
      judgT zero (numT (encExpr e)) (numT (encExpr e)) (numT (encExpr (all Q))))) :
    Thm env [] (∀ₒ k, prfT T (instT (numT (encExpr Q)) (litT k) zero)
      (ev (instCertC z s Q e c) [k]) =ₒ zero) := by
  have jc' : ∀ {Γ}, Thm env Γ (jT (numT c) =ₒ judgT zero (numT (encExpr e)) (numT (encExpr e))
      (tagT 7 5 (pair (numT (encExpr nat)) (numT (encExpr Q))))) := by
    intro Γ; orw [jc.weak0, numT_all]
  have hn := numCert_c hz jz hs js
  ointro
  have hk := Thm.allE (hn.weak0 (Γ := [nat])) (t := .bvar 0) (.bvar .zero)
  simp only [obj_simp] at hk
  ocases hk with h1 h2
  simp only [instCertC]
  orw [ev_appC (by otype)]
  simp only [ev_numC_ctx]
  exact prfT_of_cert (by otype) (by otype) (by otype)
    (certT_appT (by otype) (by otype) (by otype) (by otype) (by otype) (by otype) (by otype)
      (by otype) (by otype) rfl hc.weak0 h1 jc' h2)
    (jT_appT (by otype) (by otype) (by otype) (by otype) (by otype) (by otype) (by otype)
      (by otype) (by otype))

end

/-- **Internal instantiation**, from provability: for a closed provable `∀ x : Nat, Q` there is a
code `σ` with, internally, `∀ k, Prf(⌜Q⌝[k], σ k)`. -/
theorem internal_inst {envT : VEnv} {T : Tables} (hT : TablesFor envT T) (H : HasNat envT)
    {Q : VExpr} (hQ : Provable envT (all Q)) :
    ∃ σ : PR, ∀ {env : VEnv} [ObjEnv env],
      Thm env [] (∀ₒ k, prfT T (instT (numT (encExpr Q)) (litT k) zero) (ev σ [k]) =ₒ zero) := by
  obtain ⟨z, hz⟩ := closed_cert hT (H.zeroT (U := 0) (Γ := []))
  obtain ⟨s, hs⟩ := closed_cert hT (H.succT (U := 0) (Γ := []))
  obtain ⟨e, c, hc⟩ := provable_cert hT hQ
  exact ⟨instCertC z s Q e c, fun {env} _ =>
    inst_c (hz (env := env)).1 (hz (env := env)).2 (hs (env := env)).1 (hs (env := env)).2
      (hc (env := env)).1 (hc (env := env)).2⟩

end Incomplete.Obj
