import Incomplete.Obj.Loeb

/-!
# A consistent, ω-inconsistent context

Over a consistent `env`, the context `[Prov T ⊥]`, the hypothesis that some certificate checks as a
proof of `⊥` under `env`'s checker, is consistent (`loeb` at `P := ⊥`: a derivation of `⊥` from
`Prov T ⊥` is a proof of `Prov T ⊥ → ⊥`), proves `∃ k, Prf(⌜⊥⌝, k)`, and refutes
`Prf(⌜⊥⌝, k)` at every numeral `k`: the checker's value there is a nonzero numeral, provably
(`prov_lit`, `chkNum_eq_zero`). The result is `omega_inconsistent`.
-/

namespace Incomplete
open Lean4Lean Obj

section
variable {env : VEnv} {T : Tables}

/-- In a consistent theory, `Prov T ⊥ → ⊥` is unprovable in context: `[Prov T ⊥]` is
consistent. -/
theorem prov_false_ctx_consistent (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) : ¬Thm env [Prov T falseS] falseS := by
  intro h
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  have hi : Thm env [] (imp (Prov T falseS) falseS) := Thm.intro (by otype) h
  exact hC (loeb env hwf hext hT falseT hi.provable)

/-- The hypothesis `Prov T ⊥`, as a theorem of its context. -/
theorem prov_false_ctx_proves_prov [ObjEnv env] : Thm env [Prov T falseS] (Prov T falseS) :=
  (Thm.hyp .zero).cast (Prov_closed' T falseS).lift_eq

/-- In a consistent theory, each numeral is provably not a certificate of `⊥`. -/
theorem not_prf_false_lit [ObjEnv env] (hT : TablesFor env T) (hC : Consistent env) (k : Nat) :
    Provable env (neg (prfT T (numT (encExpr falseS)) (lit k) =ₒ zero)) := by
  have e := prov_lit (env := env) T falseS k
  have hm : chkNumFor T (fun _ => true) (encExpr falseS) k ≠ 0 :=
    fun h0 => hC ((chkNum_eq_zero hT falseS).1 ⟨k, h0⟩)
  generalize chkNumFor T (fun _ => true) (encExpr falseS) k = m at e hm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  refine Thm.provable (Thm.intro (by otype) ?_)
  have h : Thm env [prfT T (numT (encExpr falseS)) (lit k) =ₒ zero]
      (prfT T (numT (encExpr falseS)) (lit k) =ₒ zero) :=
    (Thm.hyp .zero).cast (by simp only [obj_simp])
  orw [e.weak0] at h
  exact (succ_ne_zero (litTy m)).mp h

/-- **A consistent, ω-inconsistent context.** Over a consistent well-formed extension of
`natEnv`, the context `[Prov T ⊥]` is consistent, proves `∃ k, Prf(⌜⊥⌝, k)`, and refutes
`Prf(⌜⊥⌝, k)` at every numeral `k`. -/
theorem omega_inconsistent (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hC : Consistent env) :
    ¬Thm env [Prov T falseS] falseS ∧
    Thm env [Prov T falseS] (Prov T falseS) ∧
    ∀ k : Nat, Thm env [Prov T falseS] (neg (prfT T (numT (encExpr falseS)) (lit k) =ₒ zero)) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  exact ⟨prov_false_ctx_consistent env hwf hext hT hC, prov_false_ctx_proves_prov,
    fun k => Thm.weak0 (not_prf_false_lit hT hC k)⟩

/-- `omega_inconsistent` for tables that every well-formed `env` admits. -/
theorem omega_inconsistent_exists (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    (hC : Consistent env) :
    ∃ T, TablesFor env T ∧ ¬Thm env [Prov T falseS] falseS ∧
      Thm env [Prov T falseS] (Prov T falseS) ∧
      ∀ k : Nat, Thm env [Prov T falseS] (neg (prfT T (numT (encExpr falseS)) (lit k) =ₒ zero)) := by
  obtain ⟨T, hT⟩ := hwf.checkable.tables
  exact ⟨T, hT, omega_inconsistent env hwf hext hT hC⟩

end

end Incomplete
