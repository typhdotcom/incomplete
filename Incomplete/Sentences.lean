import Incomplete.Adequacy

/-!
# Halting sentences and Σ₁-completeness

`notHalts f n` is the closed proposition `∀ k : Nat, IsZero (f k n) → False`, with `False` and
`True` impredicatively encoded and `IsZero` by large elimination, so that `Nat` is the only
inductive type it needs. `halts f n` is its negation. Every true `halts` sentence is provable
(`halts_provable`), and the two are never both provable unless `False` is (`refute`).
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

def falseS : VExpr := .forallE (.sort .zero) (.bvar 0)
def trueS : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))
def trueI : VExpr := .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

/-- `Nat.rec True (fun _ _ => False) n`, as a family of propositions. -/
def isZero (n : VExpr) : VExpr :=
  natRec (.sort .zero) trueS (.lam nat (.lam (.sort .zero) falseS)) n

def notHalts (f : PR) (n : Nat) : VExpr :=
  .forallE nat (.forallE (isZero (.app (.app (fn f) (lit n)) (.bvar 0))) falseS)

def halts (f : PR) (n : Nat) : VExpr := .forallE (notHalts f n) falseS

/-- Provability in the object theory: a closed term of the proposition, with no universe
parameters. -/
theorem isZero_inst (n a : VExpr) : (isZero n).inst a = isZero (n.inst a) := rfl

def Provable (env : VEnv) (P : VExpr) : Prop := ∃ e, env.HasType 0 [] e P

section
variable {env : VEnv}

theorem prop_eq : env.IsDefEq 0 Γ (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
    (.sort (.succ (.imax (.succ .zero) .zero))) :=
  .sortDF ⟨trivial, trivial⟩ trivial (VLevel.equiv_def.2 fun _ => rfl)

theorem falseT : env.HasType 0 Γ falseS (.sort .zero) :=
  prop_eq.defeq (HasType.forallE (.sort trivial) (.bvar .zero))

theorem trueT : env.HasType 0 Γ trueS (.sort .zero) := by
  have h1 : env.HasType 0 (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have h2 : env.HasType 0 (.bvar 0 :: .sort .zero :: Γ) (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have h3 : env.HasType 0 (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1)) (.sort .zero) :=
    .defeqDF (.sortDF (l := .imax .zero .zero) ⟨trivial, trivial⟩ trivial
      (VLevel.equiv_def.2 fun _ => rfl)) (HasType.forallE h1 h2)
  exact prop_eq.defeq (HasType.forallE (.sort trivial) h3)

theorem trueI_T : env.HasType 0 Γ trueI trueS :=
  HasType.lam (.sort trivial) (HasType.lam (.bvar .zero) (.bvar .zero))

end

section
variable {env : VEnv} (H : HasNat env) (henv : env.Ordered)
include H

theorem isZeroStepT : env.HasType 0 Γ (.lam nat (.lam (.sort .zero) falseS))
    (.forallE nat (.forallE (.sort .zero) (.sort .zero))) :=
  HasType.lam H.natT (HasType.lam (.sort trivial) falseT)

theorem isZero_congr (hn : env.IsDefEq 0 Γ n n' nat) :
    env.IsDefEq 0 Γ (isZero n) (isZero n') (.sort .zero) :=
  H.natRec_congr Inert.sort (fun _ => .sort trivial) trueT (isZeroStepT H) hn

include henv

theorem notHaltsT (f : PR) (n : Nat) : env.IsType 0 [] (notHalts f n) :=
  ⟨_, HasType.forallE H.natT (HasType.forallE
    (H.natRecT Inert.sort (fun _ => .sort trivial) trueT (isZeroStepT H)
      (.app' (.app' ((fnT H henv f).weak0 henv) (H.litT n) rfl) (.bvar .zero) rfl))
    falseT)⟩


/-- **Σ₁-completeness.** A true halting sentence is provable. -/
theorem halts_provable {f : PR} {n : Nat} (hf : f.Halts n) : Provable env (halts f n) := by
  obtain ⟨k, hk⟩ := hf
  obtain ⟨_, hP⟩ := notHaltsT H henv f n
  have hc : (notHalts f n).ClosedN := hP.closedN henv trivial
  have h0 : env.HasType 0 [notHalts f n] (.bvar 0) (notHalts f n) := by
    have : env.HasType 0 [notHalts f n] (.bvar 0) (notHalts f n).lift := .bvar .zero
    rwa [show (notHalts f n).lift = notHalts f n from hc.liftN_eq (Nat.zero_le _)] at this
  have h1 : env.HasType 0 [notHalts f n] (.app (.bvar 0) (lit k))
      (.forallE (isZero (.app (.app (fn f) (lit n)) (lit k))) falseS) := by
    refine .app' h0 (H.litT k) ?_
    have hf : (fn f).ClosedN := (fnT H henv f).closedN henv trivial
    show VExpr.forallE ((isZero _).inst (lit k)) (falseS.inst (lit k) 1) = _
    rw [isZero_inst]
    simp [VExpr.inst, hf.instN_eq (Nat.zero_le _), (Inert.lit n).inst]; rfl
  have hconv : env.IsDefEq 0 [] (isZero (.app (.app (fn f) (lit n)) (lit k))) trueS
      (.sort .zero) := by
    have := isZero_congr H (fn_adequate H henv f n k)
    rw [hk] at this
    exact this.trans (H.iota_zero henv Inert.sort (fun _ => .sort trivial) trueT (isZeroStepT H))
  have h2 := HasType.app h1 ((hconv.weak0 henv).symm.defeq trueI_T)
  exact ⟨_, HasType.lam hP h2⟩

end

/-- A proof of `halts f n` applied to one of `notHalts f n` proves `False`. -/
theorem refute {env : VEnv} {f : PR} {n : Nat} :
    Provable env (halts f n) → Provable env (notHalts f n) → Provable env falseS
  | ⟨_, hp⟩, ⟨_, hq⟩ => ⟨_, .app' hp hq rfl⟩

end Incomplete
