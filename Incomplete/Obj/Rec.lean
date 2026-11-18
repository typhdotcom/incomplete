import Incomplete.Obj.Tactic
import Incomplete.Obj.Iota

/-!
# Binary functions by primitive recursion

`rec2 z s` is `fun a b => Nat.rec z[a] (fun y r => s[a, y, r]) b`. In a well-formed context it
computes by beta and iota (`rec2_zero`, `rec2_succ`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

/-- `fun a b => Nat.rec z[a] (fun y r => s[a, y, r]) b`, with `z` over `[a]` and `s` over
`[r, y, a]`. -/
def rec2 (z s : VExpr) : VExpr :=
  .lam nat (.lam nat (natRec nat z.lift (.lam nat (.lam nat (s.liftN 1 2))) (.bvar 0)))

/-- The step `fun y r => s[a, y, r]` at `a`. -/
def rec2Step (s a : VExpr) : VExpr := .lam nat (.lam nat (s.inst a 2))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {z s a b y : VExpr}

theorem rec2Ty (hz : env.HasType (nat :: Γ) z nat) (hs : env.HasType (nat :: nat :: nat :: Γ) s nat) :
    env.HasType Γ (rec2 z s) (.forallE nat (.forallE nat nat)) :=
  .lam natTy (.lam natTy (natRecT Inert.nat (fun _ => natTy) (weakTy hz)
    (.lam natTy (.lam natTy (hs.weakN (.succ (.succ .one))))) (.bvar .zero)))

theorem rec2StepTy (hs : env.HasType (nat :: nat :: nat :: Γ) s nat) (ha : env.HasType Γ a nat) :
    env.HasType Γ (rec2Step s a) (.forallE nat (.forallE nat nat)) :=
  .lam natTy (.lam natTy (hs.instN (.succ (.succ .zero)) ha))

/-- `rec2 z s a b ≡ Nat.rec z[a] (rec2Step s a) b`, by beta. -/
theorem rec2_beta (hz : env.HasType (nat :: Γ) z nat)
    (hs : env.HasType (nat :: nat :: nat :: Γ) s nat)
    (ha : env.HasType Γ a nat) (hb : env.HasType Γ b nat) :
    env.IsDefEq Γ (app2 (rec2 z s) a b) (natRec nat (z.inst a) (rec2Step s a) b) nat := by
  have hbody : env.HasType (nat :: nat :: Γ)
      (natRec nat z.lift (.lam nat (.lam nat (s.liftN 1 2))) (.bvar 0)) nat :=
    natRecT Inert.nat (fun _ => natTy) (weakTy hz)
      (.lam natTy (.lam natTy (hs.weakN (.succ (.succ .one))))) (.bvar .zero)
  have b1 := IsDefEq.beta (HasType.lam natTy hbody) ha
  have b1' := IsDefEq.appDF b1 hb
  have hbody' := hbody.instN (.succ .zero) ha
  have b2 := IsDefEq.beta hbody' hb
  refine b1'.trans (b2.trans ?_)
  have e1 : ((s.liftN 1 2).inst a 3).inst b 2 = s.inst a 2 := by
    rw [show (3 : Nat) = 1 + 2 from rfl, ← liftN_instN_lo 1 s a 2 2 (Nat.le_refl _), inst_liftN]
  simp only [natRec_inst, VExpr.inst, instVar, Inert.nat.inst, ← lift_instN_lo, inst_lift, e1]
  simp only [obj_simp, rec2Step]
  exact (natRecT Inert.nat (fun _ => natTy) (hz.instN .zero ha)
    (rec2StepTy hs ha) hb)

theorem rec2_zero (hz : env.HasType (nat :: Γ) z nat)
    (hs : env.HasType (nat :: nat :: nat :: Γ) s nat) (ha : env.HasType Γ a nat) :
    env.IsDefEq Γ (app2 (rec2 z s) a zero) (z.inst a) nat :=
  (rec2_beta hz hs ha zeroTy).trans (natRec_zero' (A := nat) Inert.nat (fun _ => natTy)
    (instTy hz ha) (rec2StepTy hs ha))

theorem rec2_succ (hz : env.HasType (nat :: Γ) z nat)
    (hs : env.HasType (nat :: nat :: nat :: Γ) s nat) (ha : env.HasType Γ a nat)
    (hy : env.HasType Γ y nat) :
    env.IsDefEq Γ (app2 (rec2 z s) a (S y))
      (((s.inst a 2).inst y 1).inst (app2 (rec2 z s) a y)) nat := by
  have hF : env.HasType Γ (app2 (rec2 z s) a y) nat := app2Ty (rec2Ty hz hs) ha hy
  have hX : env.HasType (nat :: nat :: Γ) (s.inst a 2) nat := hs.instN (.succ (.succ .zero)) ha
  have hX' : env.HasType (nat :: Γ) ((s.inst a 2).inst y 1) nat := hX.instN (.succ .zero) hy
  have hSt := rec2StepTy hs ha
  have i := natRec_succ' (A := nat) Inert.nat (fun _ => natTy) (instTy hz ha) hSt hy
  have c := IsDefEq.appDF (HasType.app hSt hy) (rec2_beta hz hs ha hy).symm
  have b1 := IsDefEq.appDF (IsDefEq.beta (HasType.lam natTy hX) hy) hF
  have b2 := IsDefEq.beta hX' hF
  exact (rec2_beta hz hs ha (STy hy)).trans (i.trans (c.trans (b1.trans b2)))

end

end Incomplete.Obj
