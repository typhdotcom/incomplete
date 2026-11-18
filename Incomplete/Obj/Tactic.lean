import Incomplete.Obj.Core
import Batteries.Tactic.PermuteGoals

/-!
# Tactics for object-level proofs

On goals `Thm env Γ P`:

- `onorm` normalizes lifts and instantiations in the goal.
- `ointro` introduces an implication or a `∀`; `oind` starts an induction on the `∀`.
- `ohyp` closes the goal by a hypothesis in `Γ`; `orefl` by reflexivity.
- `orw [h, ← h']` rewrites by equations `h : ∀ …, Thm env Γ (EqN a b)`, abstracting the
  outermost occurrences of the left side (instantiating its metavariables at the first match) and
  proving the motive's typing and the rule's typing premises by `otype`.
-/

namespace Incomplete.Obj
open Lean Meta Elab Tactic
open Lean4Lean

macro "onorm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [obj_simp] $[$loc]?)

macro "ointro" : tactic => `(tactic|
  first
  | refine Thm.allI ?_
  | (refine Thm.intro ?_ ?_; otype; try onorm))

/-- Introduce an implication, with `h` the hypothesis in the extended context. -/
macro "ointro " h:ident : tactic => `(tactic|
  (refine Thm.introH ?_ fun $h => ?_; otype; try onorm at $h:ident ⊢))

/-- Instantiate a closed `∀`-theorem at terms with the given typings. -/
macro "ospec " h:term:max hs:term:max* : tactic => do
  let mut t ← `(Thm.weak0 $h)
  for x in hs do t ← `(Thm.allE $t $x)
  `(tactic| (have h' := $t; (try onorm at h'); exact h'))

macro "oind" : tactic => `(tactic|
  (refine Thm.ind ?_ ?_ ?_; otype; (try onorm); on_goal 2 => try onorm))

macro "ohyp" : tactic => `(tactic| (apply Thm.hyp; lookup_tac))

macro "orefl" : tactic => `(tactic| (refine Thm.refl ?_; otype))

/-- The motive body `M` with `M.inst a d = e`, abstracting the occurrences of `a` at depth 0. -/
partial def absMotive (a : Expr) (d : Nat) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if d == 0 then
    if ← withReducible (isDefEq e a) then return mkApp (mkConst ``VExpr.bvar) (toExpr d)
  let fn := e.getAppFn
  let args := e.getAppArgs
  let liftLeaf : MetaM Expr :=
    return mkApp3 (mkConst ``VExpr.liftN) (toExpr 1) e (toExpr d)
  match fn with
  | .const c _ =>
    if c == ``VExpr.bvar && args.size == 1 then
      match args[0]!.nat? with
      | some i => return mkApp (mkConst ``VExpr.bvar) (toExpr (if i < d then i else i + 1))
      | none => liftLeaf
    else if (c == ``VExpr.lam || c == ``VExpr.forallE) && args.size == 2 then
      return mkApp2 fn (← absMotive a d args[0]!) (← absMotive a (d + 1) args[1]!)
    else if c == ``Obj.all && args.size == 1 then
      return mkApp fn (← absMotive a (d + 1) args[0]!)
    else if c == ``VExpr.sort || c == ``VExpr.const then
      return e
    else
      let ty ← inferType fn
      let ok ← forallTelescopeReducing ty fun xs body => do
        if xs.size != args.size then return false
        if !(← isDefEq body (mkConst ``VExpr)) then return false
        xs.allM fun x => do isDefEq (← inferType x) (mkConst ``VExpr)
      if ok && args.size > 0 then
        return mkAppN fn (← args.mapM (absMotive a d))
      else liftLeaf
  | _ => liftLeaf

/-- Rewrite the goal `Thm env Γ G` once by `h`. -/
def orwCore (stx : Term) (symm : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let_expr Thm env Γ G := tgt | throwError "orw: goal is not `Thm env Γ P`: {tgt}"
  let h ← elabTerm stx none (mayPostpone := true)
  let hty ← instantiateMVars (← inferType h)
  let (mvs, _, body) ← forallMetaTelescopeReducing hty
  let h := mkAppN h mvs
  let body ← instantiateMVars body
  let_expr Thm env' Γ' eq := body | throwError "orw: rule is not `Thm env Γ (EqN a b)`: {body}"
  let_expr EqN a b := eq | throwError "orw: rule is not an equation: {eq}"
  unless ← isDefEq env env' do throwError "orw: environments differ"
  unless ← isDefEq Γ Γ' do throwError "orw: contexts differ: {Γ} vs {Γ'}"
  let (a, b) := if symm then (b, a) else (a, b)
  let M ← absMotive a 0 G
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  let M ← instantiateMVars M
  let hM ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``VEnv.HasType
    #[env, toExpr 0, ← mkAppM ``List.cons #[mkConst ``Incomplete.nat, Γ], M,
      mkApp (mkConst ``VExpr.sort) (mkConst ``VLevel.zero)])
  let ha ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``VEnv.HasType
    #[env, toExpr 0, Γ, a, mkConst ``Incomplete.nat])
  let hb ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``VEnv.HasType
    #[env, toExpr 0, Γ, b, mkConst ``Incomplete.nat])
  let hEq ← if symm then
      mkAppM ``Thm.symm #[hb, ha, h]
    else pure h
  let hG ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``VExpr.inst #[M, a, toExpr 0]) G)
  let rest ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Thm
    #[env, Γ, ← mkAppM ``VExpr.inst #[M, b, toExpr 0]])
  let pf ← mkAppM ``Thm.rewrite #[hM, ha, hb, hEq, hG, rest]
  goal.assign pf
  let side := (mvs.toList.filterMap fun m =>
    if m.isMVar then some m.mvarId! else none)
  let mut others := []
  for m in side do
    unless ← m.isAssigned do others := others ++ [m]
  setGoals [hG.mvarId!]
  evalTactic (← `(tactic| first | rfl | simp only [obj_simp]))
  unless ← hG.mvarId!.isAssigned do
    throwError "orw: could not check the motive{indentExpr M}\nagainst the goal{indentExpr G}"
  for g in [hM, ha, hb] do
    setGoals [g.mvarId!]
    evalTactic (← `(tactic| (try simp only [obj_simp]) <;> otype))
  let mut left := []
  for m in others do
    unless ← m.isAssigned do
      if (← instantiateMVars (← m.getType)).hasExprMVar then
        left := left ++ [m]
      else
        setGoals [m]
        try evalTactic (← `(tactic| otype)) catch _ => left := left ++ [m]
  setGoals ([rest.mvarId!] ++ left)
  evalTactic (← `(tactic| try simp only [obj_simp]))

syntax "orw " "[" Lean.Parser.Tactic.rwRule,* "]" : tactic

elab_rules : tactic
  | `(tactic| orw [$rs,*]) => do
    for r in rs.getElems do
      match r with
      | `(Lean.Parser.Tactic.rwRule| ← $t:term) => orwCore t true
      | `(Lean.Parser.Tactic.rwRule| $t:term) => orwCore t false
      | _ => throwUnsupportedSyntax
    evalTactic (← `(tactic| try orefl))

/-! ### Statements with named variables -/

/-- `e` with the free variables `xs` (outermost first) bound by `all`s around depth `d`. Object
binders are `VExpr.lam`, `VExpr.forallE` and `all`; every other function of `VExpr`s is taken
to keep its arguments at its own depth. -/
partial def bindVars (xs : Array Expr) (d : Nat) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some i := xs.findIdx? (· == e) then
    return mkApp (mkConst ``VExpr.bvar) (toExpr (xs.size - 1 - i + d))
  unless e.hasAnyFVar (xs.contains <| .fvar ·) do return e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    if (c == ``VExpr.lam || c == ``VExpr.forallE) && args.size == 2 then
      return mkApp2 fn (← bindVars xs d args[0]!) (← bindVars xs (d + 1) args[1]!)
    else if c == ``Obj.all && args.size == 1 then
      return mkApp fn (← bindVars xs (d + 1) args[0]!)
    else
      let ty ← inferType fn
      let ok ← forallTelescopeReducing ty fun ys body => do
        if ys.size != args.size then return false
        if !(← isDefEq body (mkConst ``VExpr)) then return false
        ys.allM fun y => do isDefEq (← inferType y) (mkConst ``VExpr)
      unless ok do throwError "∀ₒ: cannot bind variables in {e}"
      return mkAppN fn (← args.mapM (bindVars xs d))
  | _ => throwError "∀ₒ: cannot bind variables in {e}"

/-- `∀ₒ x y, P`: the object formula `all (all P)`, with `x` and `y` read as the bound
variables. -/
elab "∀ₒ " xs:ident+ ", " b:term : term => do
  let names := xs.map (·.getId)
  let decls : Array (Name × Expr) := names.map fun n => (n, mkConst ``VExpr)
  Meta.withLocalDeclsDND decls fun fvs => do
    let e ← Term.elabTermAndSynthesize b (mkConst ``VExpr)
    let mut r ← bindVars fvs 0 e
    for _ in fvs do r := mkApp (mkConst ``Obj.all) r
    return r

@[inherit_doc] scoped infix:50 " =ₒ " => EqN
@[inherit_doc] scoped infixr:25 " →ₒ " => imp

end Incomplete.Obj
