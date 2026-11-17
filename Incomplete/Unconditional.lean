import Incomplete.LeafPR
import Incomplete.ModelSound
import Incomplete.Diag

/-!
# Incompleteness without hypotheses, for the fragment with sorts `Prop` and `Type`

`BProvable natEnv` is provability in `natEnv` by derivations without the projection rules whose
sorts are at most `Type` (`BDefEq`, `Bounded.lean`). It is Σ₁-complete (`bhalts_provable`),
enumerated by a primitive recursive code (`bcheckDecidable`), consistent and sound for `halts`
sentences (both from the set model of `ModelSound.lean`). So the diagonal sentence is true and
neither provable nor refutable there, with no hypothesis left.
-/

namespace Incomplete
open Lean4Lean
open PR

/-- A code decides proofs in the fragment, as `CheckDecidable` does for an environment. -/
def BCheckDecidable : Prop :=
  ∃ G : PR, (∀ Q k ρ, G.eval (vcons (encExpr Q) (vcons k ρ)) = 0 → BProvable natEnv Q) ∧
    ∀ Q, BProvable natEnv Q → ∃ k, ∀ ρ, G.eval (vcons (encExpr Q) (vcons k ρ)) = 0

theorem bcheckDecidable : BCheckDecidable := by
  have hc : ∀ c : Cert, c.check natT.env 0 natT.deciders = c.check natEnv 0 natT.deciders :=
    Cert.check_congr (fun n => (natEnv_tables.consts n).symm)
      (fun n => (natEnv_tables.inducts n).symm) 0 _
  have hK := Tables.deciders_spec natEnv_tables
  refine ⟨andz (chkC natT fun _ => true) (PR.push (var 1) leafC), fun Q k ρ hk => ?_, fun Q hQ => ?_⟩
  · rw [eval_andz_zero, chkC_computes, PR.eval_push leafC_computes] at hk
    simp only [vcons_zero, vcons_succ, eval_var, chkNumFor, decExpr_enc] at hk
    obtain ⟨h1, h2⟩ := hk
    split at h1
    · rename_i hh
      simp only [Cert.usesOnly_all, Bool.true_and, checkProofT, Bool.and_eq_true,
        decide_eq_true_eq, hc] at hh
      obtain ⟨hk, hΓ, he, hA⟩ := hh
      have := Cert.check_bsound hK _ hk (leafNum_eq_zero.1 h2)
      rw [hΓ, hA, ← he] at this
      exact ⟨_, this⟩
    · cases h1
  · obtain ⟨e, h⟩ := hQ
    obtain ⟨c, k, b, hj⟩ := Cert.check_bcomplete hK h
    refine ⟨encCert c, fun ρ => ?_⟩
    rw [eval_andz_zero, chkC_computes, PR.eval_push leafC_computes]
    simp only [vcons_zero, vcons_succ, eval_var, chkNumFor, decExpr_enc, decCert_enc]
    refine ⟨?_, leafNum_eq_zero.2 (by rw [decCert_enc]; exact b)⟩
    simp [Cert.usesOnly_all, checkProofT, hc, k, hj]

theorem bdiagEnumerable :
    ∃ d : PR, ∀ f : PR, d.Halts f.code ↔ BProvable natEnv (notHalts f f.code) := by
  obtain ⟨G, hG1, hG2⟩ := bcheckDecidable; obtain ⟨N, hN⟩ := diagComputable
  refine ⟨.push N G, fun f => ?_⟩
  have key : ∀ k, PR.eval (.push N G) (val2 k f.code) =
      G.eval (vcons (encExpr (notHalts f f.code)) (vcons k (vcons f.code fun _ => 0))) := by
    intro k
    rw [PR.eval, hN, show val2 k f.code 1 = f.code by simp only [val2, vcons_succ, vcons_zero],
      diagNum_code]; rfl
  simp only [PR.Halts, key]
  exact ⟨fun ⟨k, hk⟩ => hG1 _ _ _ hk, fun h => let ⟨k, hk⟩ := hG2 _ h; ⟨k, hk _⟩⟩

/-- **Incompleteness, unconditionally**, for provability in `natEnv` by derivations whose sorts
are `Prop` and `Type` and that use no projection rule (`BProvable`): some machine does not halt
on its own number, and the fragment neither proves nor refutes that. -/
theorem incomplete_unconditional :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬BProvable natEnv (notHalts d d.code) ∧
      ¬BProvable natEnv (halts d d.code) := by
  obtain ⟨d, h1, h2, h3⟩ := kleene PR.code PR.Halts (BProvable natEnv) halts notHalts
    (fun _ _ h => bhalts_provable hasNat_natEnv natEnv_ordered h)
    (fun _ _ h1 h2 => bconsistent (brefute h1 h2)) bdiagEnumerable
  exact ⟨d, h1, h2, h3 fun _ _ h => bhaltsSound h⟩

end Incomplete
