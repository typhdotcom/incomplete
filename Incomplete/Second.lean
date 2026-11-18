import Incomplete.Final
import Incomplete.Rosser

/-!
# The second incompleteness theorem, reduced to its internal step

`Con T` is the non-halting sentence `notHalts (conM T) 0`, "no certificate checks as a proof of
`False`" for the checker `chkT T`, and it is true exactly when the theory is consistent
(`con_true_iff`). `G0 T` is the first theorem's sentence for the explicit diagonal machine
`dg T`, unprovable from consistency (`G0_unprovable`). So a proof of `Con T → G0 T` inside the
theory gives the second theorem (`second_of_internal`). `Obj/Second.lean` proves that internal
step (`con_imp_G0_provable`) and the theorem (`con_unprovable`, `second_incompleteness`).
-/

namespace Incomplete
open Lean4Lean
open PR

/-- The proof checker for all rules: sentence number in variable `0`, certificate in `1`. -/
noncomputable def chkT (T : Tables) : PR := chkC T (fun _ => true)

/-- Halts exactly when some certificate checks as a proof of `False`. -/
noncomputable def conM (T : Tables) : PR := push (numC (encExpr falseS)) (chkT T)

/-- **Consistency**, as a non-halting sentence: no certificate proves `False`. -/
noncomputable def Con (T : Tables) : VExpr := notHalts (conM T) 0

/-- The diagonal machine of `checkDecidable_of_tables` and `diagEnumerable_of`. -/
noncomputable def dg (T : Tables) : PR := push diagC (chkT T)

/-- The first theorem's sentence for `dg T`. -/
noncomputable def G0 (T : Tables) : VExpr := notHalts (dg T) (dg T).code

section
variable {env : VEnv} {T : Tables}

theorem eval_chkT (ρ : Val) : (chkT T).eval ρ = chkNumFor T (fun _ => true) (ρ 0) (ρ 1) :=
  chkC_computes _ ρ

theorem chkNum_eq_zero (hT : TablesFor env T) (Q : VExpr) :
    (∃ k, chkNumFor T (fun _ => true) (encExpr Q) k = 0) ↔ Provable env Q := by
  rw [provable_iff_certT hT]
  constructor
  · rintro ⟨k, hk⟩
    simp only [chkNumFor, decExpr_enc, Cert.usesOnly_all, Bool.true_and] at hk
    split at hk
    · exact ⟨_, ‹_›⟩
    · cases hk
  · rintro ⟨c, hc⟩
    exact ⟨encCert c, by simp [chkNumFor, decExpr_enc, decCert_enc, hc, Cert.usesOnly_all]⟩

/-- `Con T` is true exactly when the theory is consistent. -/
theorem con_true_iff (hT : TablesFor env T) : ¬(conM T).Halts 0 ↔ Consistent env := by
  have : (conM T).Halts 0 ↔ Provable env falseS := by
    rw [← chkNum_eq_zero hT]
    simp only [PR.Halts, conM, PR.eval, eval_chkT, eval_numC, vcons_zero, vcons_succ, val2]
  exact not_congr this

theorem dg_halts_iff (hT : TablesFor env T) (f : PR) :
    (dg T).Halts f.code ↔ Provable env (notHalts f f.code) := by
  rw [← chkNum_eq_zero hT]
  simp only [PR.Halts, dg, PR.eval, eval_chkT, eval_diagC, val2, vcons_zero, vcons_succ,
    diagNum_code]

/-- The first incompleteness theorem for `dg T`. -/
theorem G0_unprovable (H : HasNat env) (henv : env.Ordered) (hT : TablesFor env T)
    (hC : Consistent env) : ¬Provable env (G0 T) := fun h =>
  hC.notHaltsSound H henv _ _ h ((dg_halts_iff hT _).2 h)

theorem notHalts_prop (H : HasNat env) (henv : env.Ordered) (f : PR) (n : Nat) :
    env.HasType 0 [] (notHalts f n) (.sort .zero) :=
  forallE_prop H.natT (nonzeroT H (fn_app_T H henv _ _ (.bvar .zero)))

/-- `Con T` is a closed proposition. -/
theorem ConT (H : HasNat env) (henv : env.Ordered) : env.HasType 0 [] (Con T) (.sort .zero) :=
  notHalts_prop H henv _ _

/-- **The second incompleteness theorem**, from its internal step: if the theory proves
`Con T → G0 T` and is consistent, it does not prove `Con T`. -/
theorem second_of_internal (H : HasNat env) (henv : env.Ordered) (hT : TablesFor env T)
    (hI : Provable env (.forallE (Con T) (G0 T))) (hC : Consistent env) :
    ¬Provable env (Con T) := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi⟩ := hI
  have hcl : (G0 T).ClosedN := (notHalts_prop H henv _ _).closedN henv trivial
  exact G0_unprovable H henv hT hC ⟨_, .app' hi hc (hcl.instN_eq (Nat.zero_le _))⟩

/-- `second_of_internal` for a well-formed extension of `natEnv`. -/
theorem second_of_internal_wf (hwf : env.WF) (hext : natEnv ≤ env) (hT : TablesFor env T)
    (hI : Provable env (.forallE (Con T) (G0 T))) (hC : Consistent env) :
    ¬Provable env (Con T) :=
  second_of_internal (hasNat_natEnv.mono hext) hwf.ordered hT hI hC

end

end Incomplete
