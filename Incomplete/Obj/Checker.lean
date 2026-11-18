import Incomplete.Obj.Leaf
import Incomplete.Obj.Reduce

/-!
# Checking codes

A code `T` read as a proof checker, `Prf(s, c) := T(s, c) = 0` (`prf`), is a checker for the
object theory `env` (`IsChecker env T`) when it reads two variables, every closed theorem has a
certificate the theory proves to check, and the theory proves the two forms of modus ponens on
certificates and instantiation at numerals, the last through numeral certificates
`numCert z s`. The provability-logic development runs over such a code. The full checker
`chkT T` of tables for `env`'s environment is one (`IsChecker.full`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- Instantiation of a template proof at a numeral `a`, by modus ponens with `numCert z s a`. -/
def AllH (env : Typing) [ObjEnv env] (T : PR) (z s : Nat) : Prop :=
  ∀ {Γ ys : List VExpr} {P c a : VExpr}, Tms env Γ ys → Tm env Γ c → Tm env Γ a →
    Thm env Γ (prf T (tmplH (ys.map litT) (all P) 0) c =ₒ zero) →
    Thm env Γ (prf T (tmplH ((a :: ys).map litT) P 0) (mpX c (numCert z s a)) =ₒ zero)

/-- `T` is a proof checker for `env` that `env` reasons about. -/
structure IsChecker (env : Typing) [ObjEnv env] (T : PR) : Prop where
  bnd : bnd T ≤ 2
  closed : ∀ {P : VExpr}, Thm env [] P →
    ∃ c : Nat, ∀ {Γ : List VExpr}, Thm env Γ (prf T (numT (encExpr P)) (numT c) =ₒ zero)
  mpH : ∀ {Γ ys : List VExpr} {P Q c₁ c₂ : VExpr}, Tms env Γ ys → Tm env Γ c₁ → Tm env Γ c₂ →
    Thm env Γ (prf T (tmplH (ys.map litT) (imp P Q) 0) c₁ =ₒ zero) →
    Thm env Γ (prf T (tmplH (ys.map litT) P 0) c₂ =ₒ zero) →
    Thm env Γ (prf T (tmplH (ys.map litT) Q 0) (mpX c₁ c₂) =ₒ zero)
  allH : ∃ z s : Nat, AllH env T z s
  mpT : ∀ {Γ : List VExpr} {A B c₁ c₂ : VExpr}, B.ClosedN → Tm env Γ c₁ → Tm env Γ c₂ →
    Thm env Γ (prf T (numT (encExpr (imp A B))) c₁ =ₒ zero) →
    Thm env Γ (prf T (numT (encExpr A)) c₂ =ₒ zero) →
    Thm env Γ (prf T (numT (encExpr B)) (mpT A B (fldT 1 (jT c₁)) (fldT 1 (jT c₂)) c₁ c₂) =ₒ zero)

/-- `T` accepts only theorems of `env`. -/
def CheckSound (env : Typing) (T : PR) : Prop :=
  ∀ (P : VExpr) (k : Nat), T.eval (vcons (encExpr P) (vcons k fun _ => 0)) = 0 → Thm env [] P

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {T : PR}

/-- A closed theorem has a certificate proving it, at the template of its sentence. -/
theorem IsChecker.closed_prf (hT : IsChecker env T) {P : VExpr} (h : Thm env [] P) :
    ∃ c : Nat, ∀ {Γ : List VExpr}, Thm env Γ (prf T (tmplH [] P 0) (numT c) =ₒ zero) := by
  obtain ⟨c, hc⟩ := hT.closed h
  exact ⟨c, fun {Γ} => prf_congr (by otype) (by otype) (by otype)
    (Thm.symm (by otype) (by otype) (tmplH_nil P 0)) hc⟩

/-- **Instantiating a closed `∀ x₁ … xₘ, P`** at the values of the codes `as`, outermost first:
the holes are the values in reverse, then those of the template it started from. -/
theorem prf_instL {z s : Nat} (hA : AllH env T z s) (as : List PR) {ys : List VExpr} {c : PR}
    {P : VExpr} (hl : Tms env Γ l) (hys : Tms env Γ ys)
    (h : Thm env Γ (prf T (tmplH (ys.map litT) (allN as.length P) 0) (ev c l) =ₒ zero)) :
    Thm env Γ (prf T (tmplH (((as.map (ev · l)).reverse ++ ys).map litT) P 0)
      (ev (as.foldl (fun c a => mpP c (push a (numCertC z s))) c) l) =ₒ zero) := by
  induction as generalizing ys c with
  | nil =>
    simpa only [List.length_nil, allN, List.map_nil, List.reverse_nil, List.nil_append,
      List.foldl_nil] using h
  | cons a as ih =>
    simp only [List.length_cons, allN] at h
    have h1 : Thm env Γ (prf T (tmplH ((ev a l :: ys).map litT) (allN as.length P) 0)
        (ev (mpP c (push a (numCertC z s))) l) =ₒ zero) := by
      have := hA hys (evTy hl) (evTy (f := a) hl) h
      refine prf_congr_c (by otype) (by otype) (by otype) ?_ this
      orw [ev_mpP hl, ev_push_numCert hl]
    have := ih (ys := ev a l :: ys) (c := mpP c (push a (numCertC z s))) (.cons (evTy hl) hys) h1
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append, List.foldl_cons] at this ⊢
    exact this

end

/-! ### The full checker -/

section
variable {env : Typing} [E : ObjEnv env] {T : Tables}

/-- The full checker of tables for `env`'s environment is a checker for `env`. -/
theorem IsChecker.full (hT : TablesFor env.env T) : IsChecker env (chkT T) where
  bnd := bnd_chkT T
  closed {P} h := by
    obtain ⟨e, c, hc⟩ := provable_cert hT h.toFull
    exact ⟨c, fun {Γ} => prfT_of_cert (T := T) (s := numT (encExpr P)) (e := numT (encExpr e))
      (by otype) (by otype) (by otype) (hc (env := env) (Γ := Γ)).1 (hc (env := env) (Γ := Γ)).2⟩
  mpH hys hc₁ hc₂ h₁ h₂ := prf_mpH hys hc₁ hc₂ h₁ h₂
  allH := by
    obtain ⟨z, hz⟩ := closed_cert hT (E.hasNat.zeroT (U := 0) (Γ := []))
    obtain ⟨s, hs⟩ := closed_cert hT (E.hasNat.succT (U := 0) (Γ := []))
    exact ⟨z, s, fun hys hc ha h => prf_allH (hz (env := env) (Γ := [])).1
      (hz (env := env) (Γ := [])).2 (hs (env := env) (Γ := [])).1 (hs (env := env) (Γ := [])).2
      hys hc ha h⟩
  mpT hB hc₁ hc₂ h₁ h₂ := prf_mpT hB hc₁ hc₂ h₁ h₂

end

end Incomplete.Obj
