import Incomplete.Extend
import Lean4Lean.Theory.Typing.Meta
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# `natEnv` with `Eq`

`eqDecl` is Lean's `Eq.{u} : {α : Sort u} → α → α → Prop` with `Eq.refl`, as an inductive
declaration; `eqEnv` adds it to `natEnv`. Its recursor and iota rule are the generated ones.
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

def eqTyE : VExpr := .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
def reflTyE : VExpr := .forallE (.sort (.param 0)) (.forallE (.bvar 0)
  (.appN (.const ``Eq [.param 0]) [.bvar 1, .bvar 0, .bvar 0]))

def eqDecl : VInductDecl :=
  ⟨1, [.sort (.param 0), .bvar 0], .zero,
    [⟨``Eq, eqTyE, [.bvar 1], [⟨``Eq.refl, reflTyE, [], [.bvar 0]⟩], none⟩], false, true, false, []⟩

def eqRecTy : VExpr :=
  .foralls [.sort (.param 1), .bvar 0,
    .forallE (.bvar 1) (.forallE (.appN (.const ``Eq [.param 1]) [.bvar 2, .bvar 1, .bvar 0])
      (.sort (.param 0))),
    .app (.appN (.bvar 0) [.bvar 1]) (.appN (.const ``Eq.refl [.param 1]) [.bvar 2, .bvar 1]),
    .bvar 3]
    (.forallE (.appN (.const ``Eq [.param 1]) [.bvar 4, .bvar 3, .bvar 0])
      (.app (.appN (.bvar 3) [.bvar 1]) (.bvar 0)))

theorem eqDecl_largeElim : eqDecl.LargeElim := rfl

theorem eqDecl_recConsts : eqDecl.recConsts = [(``Eq.rec, ⟨2, eqRecTy⟩)] := by
  simp only [VInductDecl.recConsts, VInductDecl.recUVars, VInductDecl.recLevels,
    VInductDecl.motiveLevel, if_pos eqDecl_largeElim]
  rfl

/-- The binders of `Eq.rec` up to its minor premise. -/
def eqRecBinders : List VExpr :=
  [.sort (.param 1), .bvar 0,
    .forallE (.bvar 1) (.forallE (.appN (.const ``Eq [.param 1]) [.bvar 2, .bvar 1, .bvar 0])
      (.sort (.param 0))),
    .app (.appN (.bvar 0) [.bvar 1]) (.appN (.const ``Eq.refl [.param 1]) [.bvar 2, .bvar 1])]

def eqReflApp : VExpr := .appN (.const ``Eq.refl [.param 1]) [.bvar 3, .bvar 2]

def eqIota : VDefEq where
  uvars := 2
  lhs := .lams eqRecBinders
    (.appN (.const ``Eq.rec [.param 0, .param 1]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .bvar 2, eqReflApp])
  rhs := .lams eqRecBinders (.bvar 0)
  type := .foralls eqRecBinders (.app (.appN (.bvar 1) [.bvar 2]) eqReflApp)

theorem eqDecl_iotaRules : eqDecl.iotaRules = [eqIota] := by
  simp only [VInductDecl.iotaRules, VInductDecl.recUVars, VInductDecl.recLevels,
    VInductDecl.motiveLevel, if_pos eqDecl_largeElim]
  rfl

def eqEnvT : VEnv := withConst natEnv ``Eq ⟨1, eqTyE⟩
def eqEnvC : VEnv := withConst eqEnvT ``Eq.refl ⟨1, reflTyE⟩
def eqEnvR : VEnv := withConst eqEnvC ``Eq.rec ⟨2, eqRecTy⟩
def eqEnvI : VEnv := eqEnvR.addDefEq eqIota

def eqEnv : VEnv :=
  { eqEnvI with inducts := fun n => match eqDecl.types.findIdx? (·.name == n) with
    | some t => some (eqDecl, t)
    | none => eqEnvI.inducts n }

theorem addInduct_eqDecl : natEnv.addInduct eqDecl = some eqEnv := by
  simp only [VEnv.addInduct, eqDecl_recConsts, eqDecl_iotaRules, Option.bind_eq_bind]
  rfl

theorem eq_typeConsts_add : natEnv.addConstList eqDecl.typeConsts = some eqEnvT := rfl
theorem eq_ctorConsts_add : eqEnvT.addConstList eqDecl.ctorConsts = some eqEnvC := rfl
theorem eq_recConsts_add : eqEnvC.addConstList eqDecl.recConsts = some eqEnvR := by
  rw [eqDecl_recConsts]; rfl

theorem eqRecTy_wf : VConstant.WF eqEnvC ⟨2, eqRecTy⟩ := by
  have : eqEnvC.constants ``Eq = some ⟨1, eqTyE⟩ := rfl
  have : eqEnvC.constants ``Eq.refl = some ⟨1, reflTyE⟩ := rfl
  unfold VConstant.WF eqRecTy
  simp only [VExpr.foralls, VExpr.appN]
  exact ⟨_, by unfold eqTyE reflTyE at *; type_tac⟩

theorem eqIota_wf : eqIota.WF eqEnvR := by
  have : eqEnvR.constants ``Eq = some ⟨1, eqTyE⟩ := rfl
  have : eqEnvR.constants ``Eq.refl = some ⟨1, reflTyE⟩ := rfl
  have : eqEnvR.constants ``Eq.rec = some ⟨2, eqRecTy⟩ := rfl
  unfold eqIota eqRecBinders eqReflApp eqRecTy eqTyE reflTyE at *
  constructor <;> simp only [VExpr.lams, VExpr.foralls, VExpr.appN] at * <;> type_tac

theorem eqDecl_generatedWF : eqDecl.GeneratedWF natEnv := by
  intro envT envC envR hT hC hR
  cases hT.symm.trans eq_typeConsts_add
  cases hC.symm.trans eq_ctorConsts_add
  cases hR.symm.trans eq_recConsts_add
  rw [eqDecl_recConsts, eqDecl_iotaRules]
  refine ⟨fun p hp => ?_, fun df hdf => ?_⟩
  · simp only [List.mem_singleton] at hp; subst hp; exact eqRecTy_wf
  · simp only [List.mem_singleton] at hdf; subst hdf; exact eqIota_wf

theorem eqDecl_wf : eqDecl.WF natEnv where
  nonempty := by simp [eqDecl]
  level := trivial
  params := .cons ⟨_, HasType.sort (show VLevel.WF 1 (.param 0) by decide)⟩
    (.cons ⟨_, HasType.bvar .zero⟩ .nil)
  types T hT := by
    simp only [eqDecl, List.mem_singleton] at hT; subst hT
    exact ⟨⟨_, by unfold eqTyE; type_tac⟩, rfl⟩
  indices T hT := by
    simp only [eqDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT; exact .cons ⟨_, HasType.bvar (.succ .zero)⟩ .nil
  aux T hT := by simp [eqDecl, VInductDecl.allTypes] at hT
  ctors env' h' T hT := by
    cases h'.symm.trans eq_typeConsts_add
    have : eqEnvT.constants ``Eq = some ⟨1, eqTyE⟩ := rfl
    simp only [eqDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT
    refine ⟨⟨.cons ⟨_, HasType.bvar (.succ .zero)⟩ .nil, ⟨_, by unfold eqTyE; type_tac⟩⟩,
      fun c hc => ?_⟩
    simp only [List.mem_singleton] at hc; subst hc
    refine ⟨⟨_, by unfold reflTyE eqTyE at *; type_tac⟩,
      ⟨[.sort (.param 0), .bvar 0], [], rfl,
        .cons ⟨_, HasType.sort (show VLevel.WF 1 (.param 0) by decide)⟩
          (.cons ⟨_, HasType.bvar .zero⟩ .nil), .nil, by simp, fun P k hk => by simp at hk⟩,
      ⟨rfl, rfl⟩, fun ps Ds B _ _ k D f _ hf => by simp at hf⟩
  isRec _ T hT c hc f hf := by
    simp only [eqDecl, VInductDecl.allTypes, List.append_nil, List.mem_singleton] at hT
    subst hT; simp only [List.mem_singleton] at hc; subst hc; simp at hf
  largeElim _ := .inr ⟨_, rfl, rfl, .inr ⟨_, rfl, by simp⟩⟩

theorem eqEnv_wf : eqEnv.WF := by
  obtain ⟨ds, h⟩ := natEnv_wf
  exact ⟨_, .decl (.induct eqDecl_wf eqDecl_generatedWF addInduct_eqDecl) h⟩

theorem natEnv_le_eqEnv : natEnv ≤ eqEnv := VEnv.addInduct_le addInduct_eqDecl

/-- **Incompleteness of `natEnv` with `Eq`.** -/
theorem eqEnv_incomplete_of_consistent (hC : Consistent eqEnv) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable eqEnv (notHalts d d.code) ∧
      (HaltsSound eqEnv → ¬Provable eqEnv (halts d d.code)) :=
  incomplete_of_wf eqEnv eqEnv_wf natEnv_le_eqEnv hC

end Incomplete
