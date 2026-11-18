import Incomplete.Obj.Certs

/-!
# Closed certificates

Every derivable closed judgment has a certificate number `c` (meta-level completeness of the
checker), and the checker's verdict on it and its judgment's number are closed computations, so
by adequacy the object theory proves `certT T _ (numT c) = 0` and what `c` certifies, with no
reasoning about any rule (`closed_cert`, `provable_cert`). The number of a judgment or of an
expression with a known head is the tuple of its parts' numbers (`numT_judg`, `numT_app`, …).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

theorem numT_judg (Δ : List VExpr) (e1 e2 A : VExpr) :
    Thm env Γ (numT (encJudg ⟨Δ, e1, e2, A⟩) =ₒ judgT (numT (encList encExpr Δ)) (numT (encExpr e1))
      (numT (encExpr e2)) (numT (encExpr A))) := by
  show Thm env Γ (numT (PR.pair _ (PR.pair _ (PR.pair _ _))) =ₒ _)
  orw [numT_pair, numT_pair, numT_pair]

theorem numT_zero : Thm env Γ (numT 0 =ₒ zero) := by
  simp only [numT, numC_zero, ev_zero]; exact Thm.refl zeroTy

/-- The number of a closed judgment. -/
theorem numT_judg_nil (e1 e2 A : VExpr) :
    Thm env Γ (numT (encJudg ⟨[], e1, e2, A⟩) =ₒ
      judgT zero (numT (encExpr e1)) (numT (encExpr e2)) (numT (encExpr A))) := by
  orw [numT_judg]
  simp only [encList]
  orw [numT_zero]

theorem numT_tag7 {t : Nat} (ht : t < 7) (p : Nat) :
    Thm env Γ (numT (7 * p + t) =ₒ tagT 7 t (numT p)) := numT_tag (by decide) p t ht

theorem numT_bvar (i : Nat) : Thm env Γ (numT (encExpr (.bvar i)) =ₒ mul (lit 7) (numT i)) := by
  have h := numT_tag7 (env := env) (Γ := Γ) (by decide : 0 < 7) i
  simp only [Nat.add_zero] at h
  show Thm env Γ (numT (7 * i) =ₒ _)
  orw [h, add_zero]

theorem numT_sort (u : VLevel) :
    Thm env Γ (numT (encExpr (.sort u)) =ₒ tagT 7 1 (numT (encLevel u))) := numT_tag7 (by decide) _

theorem numT_app (f a : VExpr) : Thm env Γ (numT (encExpr (.app f a)) =ₒ
    tagT 7 3 (pair (numT (encExpr f)) (numT (encExpr a)))) := by
  show Thm env Γ (numT (7 * PR.pair _ _ + 3) =ₒ _)
  orw [numT_tag7 (by decide), numT_pair]

theorem numT_lam (A b : VExpr) : Thm env Γ (numT (encExpr (.lam A b)) =ₒ
    tagT 7 4 (pair (numT (encExpr A)) (numT (encExpr b)))) := by
  show Thm env Γ (numT (7 * PR.pair _ _ + 4) =ₒ _)
  orw [numT_tag7 (by decide), numT_pair]

theorem numT_forallE (A b : VExpr) : Thm env Γ (numT (encExpr (.forallE A b)) =ₒ
    tagT 7 5 (pair (numT (encExpr A)) (numT (encExpr b)))) := by
  show Thm env Γ (numT (7 * PR.pair _ _ + 5) =ₒ _)
  orw [numT_tag7 (by decide), numT_pair]

theorem numT_proj (s : Lean.Name) (i : Nat) (e : VExpr) : Thm env Γ (numT (encExpr (.proj s i e)) =ₒ
    tagT 7 6 (pair (numT (encName s)) (pair (numT i) (numT (encExpr e))))) := by
  show Thm env Γ (numT (7 * PR.pair _ (PR.pair _ _) + 6) =ₒ _)
  orw [numT_tag7 (by decide), numT_pair, numT_pair]

end

/-- The internal facts about a closed certificate `c` that checks against the environment of `T`:
the theory proves that it checks and what it certifies. -/
theorem closed_cert_of {envT : VEnv} {T : Tables} (hT : TablesFor envT T) (c : Cert)
    (k : c.check envT 0 T.deciders = true) {e1 e2 A : VExpr} (hj : c.j = ⟨[], e1, e2, A⟩) :
    ∀ {env : Typing} [ObjEnv env] {Γ : List VExpr},
      Thm env Γ (certT T (fun _ => true) (numT (encCert c)) =ₒ zero) ∧
      Thm env Γ (jT (numT (encCert c)) =ₒ
        judgT zero (numT (encExpr e1)) (numT (encExpr e2)) (numT (encExpr A))) := by
  have hc : c.check T.env 0 T.deciders = true := by
    rw [Cert.check_congr (fun n => (hT.consts n).symm) (fun n => (hT.inducts n).symm)]; exact k
  have h0 : certNum T (fun _ => true) (encCert c) = 0 :=
    certNum_eq_zero.2 (by simp [decCert_enc, Cert.usesOnly_all, hc])
  refine fun {env} _ {Γ} => ⟨?_, ?_⟩
  · have h1 := ev_lits (env := env) (Γ := Γ) (certC T (fun _ => true)) [encCert c]
    rw [certC_computes] at h1
    simp only [List.getD_cons_zero, h0, lit_zero, List.map_cons, List.map_nil] at h1
    orw [numT_lit]; exact h1
  · have h1 := ev_lits (env := env) (Γ := Γ) (childJC (var 0)) [encCert c]
    rw [eval_childJC, eval_var] at h1
    simp only [List.getD_cons_zero, j_enc, hj, List.map_cons, List.map_nil] at h1
    have h2 := ev_childJC (env := env) (Γ := Γ) (p := var 0) (l := [lit (encCert c)]) (by otype)
    simp only [obj_simp] at h2
    orw [numT_lit, ← h2, h1, ← numT_lit, numT_judg_nil]

/-- **Closed judgments are free.** A judgment derivable in the environment of `T` has a
certificate number `c` that the object theory proves to check and to certify it. -/
theorem closed_cert {envT : VEnv} {T : Tables} (hT : TablesFor envT T) {e1 e2 A : VExpr}
    (h : envT.IsDefEq 0 [] e1 e2 A) :
    ∃ c : Nat, ∀ {env : Typing} [ObjEnv env] {Γ : List VExpr},
      Thm env Γ (certT T (fun _ => true) (numT c) =ₒ zero) ∧
      Thm env Γ (jT (numT c) =ₒ
        judgT zero (numT (encExpr e1)) (numT (encExpr e2)) (numT (encExpr A))) := by
  obtain ⟨c, k, hj⟩ := Cert.check_complete (Tables.deciders_spec hT) h
  exact ⟨encCert c, closed_cert_of hT c k hj⟩

/-- **Closed theorems are free.** A closed provable `P` has a proof `e` and a certificate number
`c` that the object theory proves to check and to certify `[] ⊢ e ≡ e : P`. -/
theorem provable_cert {envT : VEnv} {T : Tables} (hT : TablesFor envT T) {P : VExpr}
    (h : Provable envT P) :
    ∃ (e : VExpr) (c : Nat), ∀ {env : Typing} [ObjEnv env] {Γ : List VExpr},
      Thm env Γ (certT T (fun _ => true) (numT c) =ₒ zero) ∧
      Thm env Γ (jT (numT c) =ₒ
        judgT zero (numT (encExpr e)) (numT (encExpr e)) (numT (encExpr P))) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, closed_cert hT he⟩

end Incomplete.Obj
