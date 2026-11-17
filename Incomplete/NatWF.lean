import Incomplete.NatEnv

/-!
# `natEnv` is ordered

Each constant's type is a type, and each iota rule's sides have its type, in the environment
before it: `natEnv` is `VEnv.Ordered`, which the substitution and weakening lemmas need.
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

theorem NatConsts.recTy {env : VEnv} (H : NatConsts env) : env.IsType 1 [] recTy := by
  have := H.hNat; have := H.hZero; have := H.hSucc
  unfold Incomplete.recTy motiveTy zeroTy succTy
  exact ⟨_, by type_tac⟩

theorem iotaZero_wf {env : VEnv} (H : NatConsts env)
    (hR : env.constants ``Nat.rec = some ⟨1, recTy⟩) : iotaZero.WF env := by
  have := H.hNat; have := H.hZero; have := H.hSucc
  unfold iotaZero recC Incomplete.recTy motiveTy zeroTy succTy at *
  constructor <;> simp only [VExpr.lams, VExpr.foralls, VExpr.appN] <;> type_tac

theorem iotaSucc_wf {env : VEnv} (H : NatConsts env)
    (hR : env.constants ``Nat.rec = some ⟨1, recTy⟩) : iotaSucc.WF env := by
  have := H.hNat; have := H.hZero; have := H.hSucc
  unfold iotaSucc recC Incomplete.recTy motiveTy zeroTy succTy at *
  constructor <;> simp only [VExpr.lams, VExpr.foralls, VExpr.appN] <;> type_tac

theorem natEnv_ordered : natEnv.Ordered := by
  have hN : envN.Ordered := .const .empty ⟨_, .sort (U := 0) (l := .succ .zero) trivial⟩ (addConst_eq rfl)
  have hZ : envZ.Ordered := .const hN ⟨_, .const' (ci := ⟨0, .sort (.succ .zero)⟩) rfl
    (by decide) rfl rfl⟩ (addConst_eq rfl)
  have hS : envS.Ordered := .const hZ ⟨_, .forallE (.const' (ci := ⟨0, .sort (.succ .zero)⟩) rfl
    (by decide) rfl rfl) (.const' (ci := ⟨0, .sort (.succ .zero)⟩) rfl (by decide) rfl rfl)⟩
    (addConst_eq rfl)
  have hR : envR.Ordered := .const hS (ci := ⟨1, recTy⟩) natConsts_envS.recTy (addConst_eq rfl)
  have hRc : NatConsts envR := natConsts_envS.mono (addConst_le (addConst_eq rfl))
  have hI0 : (envR.addDefEq iotaZero).Ordered := .defeq hR (iotaZero_wf hRc rfl)
  have hI : envI.Ordered := .defeq hI0 (iotaSucc_wf (hRc.mono addDefEq_le) rfl)
  exact .block hI (d := natDecl) rfl

end Incomplete
