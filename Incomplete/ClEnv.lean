import Incomplete.ModelSound
import Incomplete.Obj.GL

/-!
# A classical extension of `natEnv`

`clEnv` is `natEnv` with one axiom constant `dneName : dneS`, double-negation elimination. It is
well formed, extends `natEnv`, and its fragment `BProvable clEnv` proves `dneS`. The set model
interprets the axiom (`Prop` is `two`), so the fragment is consistent and sound for `halts`
sentences (`clEnv_bconsistent`, `clEnv_bhaltsSound`).
-/

namespace Incomplete
open Lean4Lean
open VExpr ZFSet Obj

/-- `natEnv` with the axiom `dneName : ∀ p : Prop, ¬¬p → p`. -/
def clEnv : VEnv := withConst natEnv dneName ⟨0, dneS⟩

theorem natEnv_dneName : natEnv.constants dneName = none := by
  rw [natEnv_tables.consts]; decide

theorem natEnv_le_clEnv : natEnv ≤ clEnv where
  constants {n a} h := by
    have hn : dneName ≠ n := by rintro rfl; rw [natEnv_dneName] at h; cases h
    simp only [clEnv, withConst, if_neg hn, h]
  defeqs h := h
  inducts h := h

theorem clEnv_wf : clEnv.WF := by
  obtain ⟨ds, h⟩ := natEnv_wf
  exact ⟨.axiom ⟨⟨0, dneS⟩, dneName⟩ :: ds,
    .decl (.axiom ⟨_, dneTy (env := natEnv)⟩ (addConst_eq natEnv_dneName)) h⟩

theorem hasNat_clEnv : HasNat clEnv := hasNat_natEnv.mono natEnv_le_clEnv

theorem clEnv_ordered : clEnv.Ordered := clEnv_wf.ordered

instance : ObjEnv clEnv := ⟨hasNat_clEnv, clEnv_ordered⟩

/-- `clEnv`'s tables. -/
def clT : Tables := { natT with consts := (dneName, ⟨0, dneS⟩) :: natT.consts }

theorem clEnv_tables : TablesFor clEnv clT where
  consts n := by
    simp only [clEnv, withConst, clT, tlookup, eq_comm (a := dneName) (b := n)]
    split <;> simp [natEnv_tables.consts]
  rules := natEnv_tables.rules
  inducts := natEnv_tables.inducts

theorem clEnv_dne : BProvable clEnv dneS :=
  ⟨.const dneName [], .const' (ci := ⟨0, dneS⟩) (by simp [clEnv, withConst]) (by simp) rfl
    (by simp) rfl⟩

/-! ### The model -/

theorem interp_dneS (ρ : Nat → ZS) : interp [] dneS ρ =
    pi two fun p => pi (pi (pi p fun _ => falseV) fun _ => falseV) fun _ => p := by
  simp [dneS, imp, neg, falseS, interp, interp_lift, univ, VLevel.eval, falseV]

theorem dneV_mem (ρ : Nat → ZS) : dneV ∈ interp [] dneS ρ := by
  rw [interp_dneS]
  refine lam_mem_pi fun p hp => lam_mem_pi fun x hx => ?_
  have hF : ∀ y, ¬y ∈ falseV := fun y hy =>
    not_mem_empty _ (app_mem_pi hy (mem_two.2 (.inl rfl)))
  rcases mem_two.1 hp with rfl | rfl
  · exact absurd (app_mem_pi hx (lam_mem_pi (f := fun _ => empty) fun y hy =>
      absurd hy (not_mem_empty _))) (hF _)
  · exact mem_single.2 rfl

theorem modelEnv_clEnv : ModelEnv clEnv where
  const {c ci} h := by
    simp only [clEnv, withConst] at h
    split at h
    · cases h; subst_vars
      refine .inr ⟨rfl, fun ρ => ?_⟩
      simp only [constV, dneName, show ¬(`Classical.dne : Lean.Name) = ``Nat by decide,
        show ¬(`Classical.dne : Lean.Name) = ``Nat.zero by decide,
        show ¬(`Classical.dne : Lean.Name) = ``Nat.succ by decide,
        show ¬(`Classical.dne : Lean.Name) = ``Nat.rec by decide, if_false, if_true]
      exact dneV_mem ρ
    · exact .inl h
  defeq h := h

/-- **Consistency** of the fragment of `clEnv`. -/
theorem clEnv_bconsistent : ¬BProvable clEnv falseS := modelEnv_clEnv.bconsistent

/-- **Soundness for `halts`** of the fragment of `clEnv`. -/
theorem clEnv_bhaltsSound {f : PR} {n : Nat} (hp : BProvable clEnv (halts f n)) : f.Halts n :=
  modelEnv_clEnv.bhaltsSound hasNat_clEnv clEnv_ordered hp

end Incomplete
