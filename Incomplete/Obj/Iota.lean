import Incomplete.Obj.Core

/-!
# Iota and `Nat.rec` congruence in any context

The iota rules of `Nat.rec` at a closed motive in `Type`, in every context (`natRec_zero`,
`natRec_succ`), and congruence in all three arguments (`natRec_congr3`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {A z z' s s' n n' : VExpr}


/-- Types a term built from sorts, variables, constants, applications, `λ` and `∀`. -/
syntax "jtype_tac" : tactic
macro_rules | `(tactic| jtype_tac) => `(tactic|
  first
  | (apply HasType.forallE <;> first | jtype_tac | decide)
  | exact HasType.sort0
  | (apply HasType.bvar; lookup_tac)
  | (apply HasType.app' <;> first | jtype_tac | exact rfl)
  | (apply HasType.const' <;> first | assumption | decide | exact rfl)
  | (apply HasType.lam <;> jtype_tac))

/-- One argument of a beta redex reached by conversion. -/
theorem beta_step {f A e B a : VExpr} (hf : env.IsDefEq Γ f (.lam A e) (.forallE A B))
    (he : env.HasType (A::Γ) e B) (ha : env.HasType Γ a A) :
    env.IsDefEq Γ (.app f a) (e.inst a) (B.inst a) :=
  (IsDefEq.appDF hf ha).trans (.beta he ha)

/-- `Nat.rec (fun _ => A) z s Nat.zero ≡ z`, at a closed motive in `Type`. -/
theorem natRec_zero' {A z s : VExpr} (hI : Inert A) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (.forallE nat (.forallE A A))) :
    env.IsDefEq Γ (natRec A z s zero) z A := by
  have := E.hasNat.hNat; have := E.hasNat.hZero; have := E.hasNat.hSucc; have := E.hasNat.hRec
  have hmI := Inert.motive hI
  have Ex : env.IsDefEq Γ (.lam motiveTy1 (.lam Incomplete.zeroTy (.lam succTy bzBody)))
      (.lam motiveTy1 (.lam Incomplete.zeroTy (.lam succTy (.bvar 1))))
      (.forallE motiveTy1 (.forallE Incomplete.zeroTy (.forallE succTy (.app (.bvar 2) zero)))) :=
    E.extra E.hasNat.hIotaZero (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
      (by simp [VLevel.eval])
  have tL3 : env.HasType (succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ) bzBody
      (.app (.bvar 2) zero) := by
    unfold bzBody succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tL2 : env.HasType (Incomplete.zeroTy :: motiveTy1 :: Γ) (.lam succTy bzBody)
      (.forallE succTy (.app (.bvar 2) zero)) := by
    unfold bzBody succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tL1 : env.HasType (motiveTy1 :: Γ) (.lam Incomplete.zeroTy (.lam succTy bzBody))
      (.forallE Incomplete.zeroTy (.forallE succTy (.app (.bvar 2) zero))) := by
    unfold bzBody succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR3 : env.HasType (succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ) (.bvar 1)
      (.app (.bvar 2) zero) := by
    unfold succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR2 : env.HasType (Incomplete.zeroTy :: motiveTy1 :: Γ) (.lam succTy (.bvar 1))
      (.forallE succTy (.app (.bvar 2) zero)) := by
    unfold succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR1 : env.HasType (motiveTy1 :: Γ) (.lam Incomplete.zeroTy (.lam succTy (.bvar 1)))
      (.forallE Incomplete.zeroTy (.forallE succTy (.app (.bvar 2) zero))) := by
    unfold succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have hm : env.HasType Γ (motive A) motiveTy1 := .lam natT (hA _)
  have ez : Incomplete.zeroTy.inst (motive A) = .app (motive A) zero := by
    simp [Incomplete.zeroTy, VExpr.inst]
  have hz' : env.HasType Γ z (Incomplete.zeroTy.inst (motive A)) := by
    rw [ez]; exact (motive_app hI hA zeroT).defeq' hz
  have es : (succTy.inst (motive A) 1).inst z = .forallE nat (.forallE (.app (motive A) (.bvar 0))
      (.app (motive A) (.app succ (.bvar 1)))) := by
    simp [succTy, VExpr.inst, instVar, hmI.liftN, hmI.inst]
  have hs' : env.HasType Γ s ((succTy.inst (motive A) 1).inst z) := by
    rw [es]; exact (succMinor_conv hI hA).defeq hs
  have W1 : Ctx.InstN Γ (motive A) motiveTy1 1 (Incomplete.zeroTy :: motiveTy1 :: Γ)
      (Incomplete.zeroTy.inst (motive A) :: Γ) := .succ .zero
  have W2 : Ctx.InstN Γ (motive A) motiveTy1 2 (succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ)
      (succTy.inst (motive A) 1 :: Incomplete.zeroTy.inst (motive A) :: Γ) := .succ (.succ .zero)
  have W2' : Ctx.InstN Γ z (Incomplete.zeroTy.inst (motive A)) 1
      (succTy.inst (motive A) 1 :: Incomplete.zeroTy.inst (motive A) :: Γ)
      ((succTy.inst (motive A) 1).inst z :: Γ) := .succ .zero
  have l1 := beta_step (Ex.trans Ex.symm) tL1 hm
  have l2 := beta_step l1 (IsDefEq.instN hm W1 tL2) hz'
  have l3 := beta_step l2 (IsDefEq.instN hz' W2' (IsDefEq.instN hm W2 tL3)) hs'
  have r1 := beta_step (Ex.symm.trans Ex) tR1 hm
  have r2 := beta_step r1 (IsDefEq.instN hm W1 tR2) hz'
  have r3 := beta_step r2 (IsDefEq.instN hz' W2' (IsDefEq.instN hm W2 tR3)) hs'
  have e3 := IsDefEq.appDF (IsDefEq.appDF (IsDefEq.appDF Ex hm) hz') hs'
  have h := l3.symm.trans (e3.trans r3)
  simp [bzBody, VExpr.appN, VExpr.inst, instVar, hmI.liftN, hmI.inst, inst_lift] at h
  exact .defeqDF (motive_app hI hA zeroT) h

/-- `Nat.rec (fun _ => A) z s (Nat.succ n) ≡ s n (Nat.rec (fun _ => A) z s n)`. -/
theorem natRec_succ' {A z s n : VExpr} (hI : Inert A) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (.forallE nat (.forallE A A)))
    (hn : env.HasType Γ n nat) :
    env.IsDefEq Γ (natRec A z s (.app succ n)) (.app (.app s n) (natRec A z s n)) A := by
  have := E.hasNat.hNat; have := E.hasNat.hZero; have := E.hasNat.hSucc; have := E.hasNat.hRec
  have hmI := Inert.motive hI
  have Ex : env.IsDefEq Γ (.lam motiveTy1 (.lam Incomplete.zeroTy (.lam succTy (.lam nat bsBodyL))))
      (.lam motiveTy1 (.lam Incomplete.zeroTy (.lam succTy (.lam nat bsBodyR))))
      (.forallE motiveTy1 (.forallE Incomplete.zeroTy (.forallE succTy (.forallE nat
        (.app (.bvar 3) (.app succ (.bvar 0))))))) :=
    E.extra E.hasNat.hIotaSucc (ls := [.succ .zero]) (by simp [VLevel.WF]) rfl
      (by simp [VLevel.eval])
  have tL4 : env.HasType (nat :: succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ) bsBodyL
      (.app (.bvar 3) (.app succ (.bvar 0))) := by
    unfold bsBodyL succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tL3 : env.HasType (succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ) (.lam nat bsBodyL)
      (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0)))) := by
    unfold bsBodyL succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tL2 : env.HasType (Incomplete.zeroTy :: motiveTy1 :: Γ) (.lam succTy (.lam nat bsBodyL))
      (.forallE succTy (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0))))) := by
    unfold bsBodyL succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tL1 : env.HasType (motiveTy1 :: Γ)
      (.lam Incomplete.zeroTy (.lam succTy (.lam nat bsBodyL)))
      (.forallE Incomplete.zeroTy (.forallE succTy (.forallE nat
        (.app (.bvar 3) (.app succ (.bvar 0)))))) := by
    unfold bsBodyL succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR4 : env.HasType (nat :: succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ) bsBodyR
      (.app (.bvar 3) (.app succ (.bvar 0))) := by
    unfold bsBodyR succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR3 : env.HasType (succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ) (.lam nat bsBodyR)
      (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0)))) := by
    unfold bsBodyR succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR2 : env.HasType (Incomplete.zeroTy :: motiveTy1 :: Γ) (.lam succTy (.lam nat bsBodyR))
      (.forallE succTy (.forallE nat (.app (.bvar 3) (.app succ (.bvar 0))))) := by
    unfold bsBodyR succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have tR1 : env.HasType (motiveTy1 :: Γ)
      (.lam Incomplete.zeroTy (.lam succTy (.lam nat bsBodyR)))
      (.forallE Incomplete.zeroTy (.forallE succTy (.forallE nat
        (.app (.bvar 3) (.app succ (.bvar 0)))))) := by
    unfold bsBodyR succTy Incomplete.zeroTy motiveTy1; jtype_tac
  have hm : env.HasType Γ (motive A) motiveTy1 := .lam natT (hA _)
  have ez : Incomplete.zeroTy.inst (motive A) = .app (motive A) zero := by
    simp [Incomplete.zeroTy, VExpr.inst]
  have hz' : env.HasType Γ z (Incomplete.zeroTy.inst (motive A)) := by
    rw [ez]; exact (motive_app hI hA zeroT).defeq' hz
  have es : (succTy.inst (motive A) 1).inst z = .forallE nat (.forallE (.app (motive A) (.bvar 0))
      (.app (motive A) (.app succ (.bvar 1)))) := by
    simp [succTy, VExpr.inst, instVar, hmI.liftN, hmI.inst]
  have hs' : env.HasType Γ s ((succTy.inst (motive A) 1).inst z) := by
    rw [es]; exact (succMinor_conv hI hA).defeq hs
  have en : ((nat.inst (motive A) 2).inst z 1).inst s = nat := rfl
  have hn' : env.HasType Γ n (((nat.inst (motive A) 2).inst z 1).inst s) := by rw [en]; exact hn
  have W1 : Ctx.InstN Γ (motive A) motiveTy1 1 (Incomplete.zeroTy :: motiveTy1 :: Γ)
      (Incomplete.zeroTy.inst (motive A) :: Γ) := .succ .zero
  have W2 : Ctx.InstN Γ (motive A) motiveTy1 2 (succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ)
      (succTy.inst (motive A) 1 :: Incomplete.zeroTy.inst (motive A) :: Γ) := .succ (.succ .zero)
  have W2' : Ctx.InstN Γ z (Incomplete.zeroTy.inst (motive A)) 1
      (succTy.inst (motive A) 1 :: Incomplete.zeroTy.inst (motive A) :: Γ)
      ((succTy.inst (motive A) 1).inst z :: Γ) := .succ .zero
  have W3 : Ctx.InstN Γ (motive A) motiveTy1 3
      (nat :: succTy :: Incomplete.zeroTy :: motiveTy1 :: Γ)
      (nat.inst (motive A) 2 :: succTy.inst (motive A) 1 :: Incomplete.zeroTy.inst (motive A) :: Γ) :=
    .succ (.succ (.succ .zero))
  have W3' : Ctx.InstN Γ z (Incomplete.zeroTy.inst (motive A)) 2
      (nat.inst (motive A) 2 :: succTy.inst (motive A) 1 :: Incomplete.zeroTy.inst (motive A) :: Γ)
      ((nat.inst (motive A) 2).inst z 1 :: (succTy.inst (motive A) 1).inst z :: Γ) :=
    .succ (.succ .zero)
  have W3'' : Ctx.InstN Γ s ((succTy.inst (motive A) 1).inst z) 1
      ((nat.inst (motive A) 2).inst z 1 :: (succTy.inst (motive A) 1).inst z :: Γ)
      (((nat.inst (motive A) 2).inst z 1).inst s :: Γ) := .succ .zero
  have l1 := beta_step (Ex.trans Ex.symm) tL1 hm
  have l2 := beta_step l1 (IsDefEq.instN hm W1 tL2) hz'
  have l3 := beta_step l2 (IsDefEq.instN hz' W2' (IsDefEq.instN hm W2 tL3)) hs'
  have l4 := beta_step l3 (IsDefEq.instN hs' W3''
    (IsDefEq.instN hz' W3' (IsDefEq.instN hm W3 tL4))) hn'
  have r1 := beta_step (Ex.symm.trans Ex) tR1 hm
  have r2 := beta_step r1 (IsDefEq.instN hm W1 tR2) hz'
  have r3 := beta_step r2 (IsDefEq.instN hz' W2' (IsDefEq.instN hm W2 tR3)) hs'
  have r4 := beta_step r3 (IsDefEq.instN hs' W3''
    (IsDefEq.instN hz' W3' (IsDefEq.instN hm W3 tR4))) hn'
  have e4 := IsDefEq.appDF (IsDefEq.appDF (IsDefEq.appDF (IsDefEq.appDF Ex hm) hz') hs') hn'
  have h := l4.symm.trans (e4.trans r4)
  simp [bsBodyL, bsBodyR, VExpr.appN, VExpr.inst, instVar, hmI.liftN, hmI.inst,
    inst_liftN_lo] at h
  exact .defeqDF (motive_app hI hA (.app' succT hn rfl)) h


theorem stepT_T (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero))) :
    env.HasType Γ (stepT A) (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallE natTy (.forallE (hA _) (hA _))

theorem natRec_zero (hc : A.ClosedN) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (stepT A)) :
    env.IsDefEq Γ (natRec A z s zero) z A := natRec_zero' (Inert.ofClosed hc) hA hz hs

theorem natRec_succ (hc : A.ClosedN) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (stepT A)) (hn : env.HasType Γ n nat) :
    env.IsDefEq Γ (natRec A z s (S n)) (.app (.app s n) (natRec A z s n)) A :=
  natRec_succ' (Inert.ofClosed hc) hA hz hs hn

theorem natRec_congr3 (hc : A.ClosedN) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.IsDefEq Γ z z' A) (hs : env.IsDefEq Γ s s' (stepT A))
    (hn : env.IsDefEq Γ n n' nat) :
    env.IsDefEq Γ (natRec A z s n) (natRec A z' s' n') A :=
  natRecDF (Inert.ofClosed hc) hA hz hs hn

end

end Incomplete.Obj
