import Incomplete.Obj.Core

/-!
# Iota and `Nat.rec` congruence in any context

The iota rules of `Nat.rec` at a closed motive in `Type`, in every context, are rules of
`ObjEnv` (`natRec_zero`, `natRec_succ`); `natRec_congr3` is congruence in all three arguments.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {A z z' s s' n n' : VExpr}

theorem stepT_T (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero))) :
    env.HasType Γ (stepT A) (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallE natTy (.forallE (hA _) (hA _))

theorem natRec_zero (hc : A.ClosedN) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (stepT A)) :
    env.IsDefEq Γ (natRec A z s zero) z A := E.natRec_zero hc hA hz hs

theorem natRec_succ (hc : A.ClosedN) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (stepT A)) (hn : env.HasType Γ n nat) :
    env.IsDefEq Γ (natRec A z s (S n)) (.app (.app s n) (natRec A z s n)) A :=
  E.natRec_succ hc hA hz hs hn

theorem natRec_congr3 (hc : A.ClosedN) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.IsDefEq Γ z z' A) (hs : env.IsDefEq Γ s s' (stepT A))
    (hn : env.IsDefEq Γ n n' nat) :
    env.IsDefEq Γ (natRec A z s n) (natRec A z' s' n') A :=
  natRecDF (Inert.ofClosed hc) hA hz hs hn

end

end Incomplete.Obj
