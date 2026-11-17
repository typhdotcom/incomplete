import Lean4Lean.Theory.Typing.Telescope
import Lean4Lean.Theory.Typing.Meta

/-!
# The object environment: `Nat`

`natDecl` is Lean's `Nat` as an inductive declaration, and `natEnv` the environment
`VEnv.addInduct` builds from it in the empty environment. Its recursor and iota rules are the
generated ones, stated here explicitly.
-/

namespace Incomplete
open Lean4Lean
open VExpr

def nat : VExpr := .const ``Nat []
def zero : VExpr := .const ``Nat.zero []
def succ : VExpr := .const ``Nat.succ []

def natDecl : VInductDecl :=
  ⟨0, [], .succ .zero,
    [⟨``Nat, .sort (.succ .zero), [],
      [⟨``Nat.zero, nat, [], []⟩,
       ⟨``Nat.succ, .forallE nat nat, [⟨nat, .succ .zero, some ⟨[], 0, []⟩⟩], []⟩], none⟩],
    true, true, false, []⟩

/-- The binders of `Nat.rec.{u}`: the motive, and the minor premises for `zero` and `succ`. -/
def motiveTy : VExpr := .forallE nat (.sort (.param 0))
def zeroTy : VExpr := .app (.bvar 0) zero
def succTy : VExpr :=
  .forallE nat (.forallE (.app (.bvar 2) (.bvar 0)) (.app (.bvar 3) (.app succ (.bvar 1))))

def recTy : VExpr :=
  .forallE motiveTy (.forallE zeroTy (.forallE succTy (.forallE nat (.app (.bvar 3) (.bvar 0)))))

def recC : VExpr := .const ``Nat.rec [.param 0]

def iotaZero : VDefEq where
  uvars := 1
  lhs := .lams [motiveTy, zeroTy, succTy] (.appN recC [.bvar 2, .bvar 1, .bvar 0, zero])
  rhs := .lams [motiveTy, zeroTy, succTy] (.bvar 1)
  type := .foralls [motiveTy, zeroTy, succTy] (.app (.bvar 2) zero)

def iotaSucc : VDefEq where
  uvars := 1
  lhs := .lams [motiveTy, zeroTy, succTy, nat]
    (.appN recC [.bvar 3, .bvar 2, .bvar 1, .app succ (.bvar 0)])
  rhs := .lams [motiveTy, zeroTy, succTy, nat]
    (.appN (.bvar 1) [.bvar 0, .appN recC [.bvar 3, .bvar 2, .bvar 1, .bvar 0]])
  type := .foralls [motiveTy, zeroTy, succTy, nat] (.app (.bvar 3) (.app succ (.bvar 0)))

theorem natDecl_largeElim : natDecl.LargeElim := rfl

theorem natDecl_recConsts : natDecl.recConsts = [(``Nat.rec, ⟨1, recTy⟩)] := by
  simp only [VInductDecl.recConsts, VInductDecl.recUVars, VInductDecl.recLevels,
    VInductDecl.motiveLevel, if_pos natDecl_largeElim]
  rfl

theorem natDecl_iotaRules : natDecl.iotaRules = [iotaZero, iotaSucc] := by
  simp only [VInductDecl.iotaRules, VInductDecl.recUVars, VInductDecl.recLevels,
    VInductDecl.motiveLevel, if_pos natDecl_largeElim]
  rfl

/-! ### The environment, stage by stage -/

/-- `VEnv.addConst`'s result when the name is fresh. -/
def withConst (env : VEnv) (n : Name) (ci : VConstant) : VEnv :=
  { env with constants := fun m => if n = m then some ci else env.constants m }

theorem addConst_eq {env : VEnv} (h : env.constants n = none) :
    env.addConst n ci = some (withConst env n ci) := by
  simp [VEnv.addConst, h, withConst]

def envN : VEnv := withConst .empty ``Nat ⟨0, .sort (.succ .zero)⟩
def envZ : VEnv := withConst envN ``Nat.zero ⟨0, nat⟩
def envS : VEnv := withConst envZ ``Nat.succ ⟨0, .forallE nat nat⟩
def envR : VEnv := withConst envS ``Nat.rec ⟨1, recTy⟩
def envI : VEnv := (envR.addDefEq iotaZero).addDefEq iotaSucc

def natEnv : VEnv :=
  { envI with inducts := fun n => match natDecl.types.findIdx? (·.name == n) with
    | some t => some (natDecl, t)
    | none => envI.inducts n }

theorem addInduct_natDecl : VEnv.empty.addInduct natDecl = some natEnv := by
  simp only [VEnv.addInduct, natDecl_recConsts, natDecl_iotaRules, Option.bind_eq_bind]
  rw [show natDecl.typeConsts = [(``Nat, ⟨0, .sort (.succ .zero)⟩)] from rfl,
    show natDecl.ctorConsts = [(``Nat.zero, ⟨0, nat⟩), (``Nat.succ, ⟨0, .forallE nat nat⟩)] from rfl]
  rfl

/-- The constants of `Nat` without its recursor. -/
structure NatConsts (env : VEnv) : Prop where
  hNat : env.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩
  hZero : env.constants ``Nat.zero = some ⟨0, nat⟩
  hSucc : env.constants ``Nat.succ = some ⟨0, .forallE nat nat⟩

/-- `Nat` with its recursor and iota rules. -/
structure HasNat (env : VEnv) : Prop extends NatConsts env where
  hRec : env.constants ``Nat.rec = some ⟨1, recTy⟩
  hIotaZero : env.defeqs iotaZero
  hIotaSucc : env.defeqs iotaSucc

theorem NatConsts.mono {env env' : VEnv} (h : env ≤ env') (H : NatConsts env) :
    NatConsts env' := ⟨h.1 H.hNat, h.1 H.hZero, h.1 H.hSucc⟩

theorem HasNat.mono {env env' : VEnv} (h : env ≤ env') (H : HasNat env) : HasNat env' :=
  ⟨H.toNatConsts.mono h, h.1 H.hRec, h.2 H.hIotaZero, h.2 H.hIotaSucc⟩

theorem natConsts_envS : NatConsts envS := ⟨rfl, rfl, rfl⟩

theorem hasNat_natEnv : HasNat natEnv := ⟨⟨rfl, rfl, rfl⟩, rfl, .inr (.inl rfl), .inl rfl⟩

end Incomplete
