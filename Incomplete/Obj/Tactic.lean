import Incomplete.Obj.Core
import Batteries.Tactic.PermuteGoals

/-!
# Tactics for object-level proofs

On goals `Thm env Γ P`:

- `onorm` normalizes lifts and instantiations in the goal.
- `ointro` introduces an implication or a `∀`; `oind` starts an induction on the `∀`.
- `ohyp` closes the goal by a hypothesis in `Γ`; `orefl` by reflexivity.
- `olift h` weakens the hypothesis `h` to the goal's context.
- `orw [h, ← h']` rewrites by equations `h : ∀ …, Thm env Γ (EqN a b)`, abstracting the
  outermost occurrences of the left side, also under object binders where they do not mention the
  bound variables (instantiating its metavariables at the first match at which the rule's
  equational premises hold by `rfl`) and proving the motive's typing and the
  rule's typing premises by `otype`; `orw [h] at h₁` rewrites the hypothesis `h₁`.
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
macro "ointro " colGt h:ident : tactic => `(tactic|
  (refine Thm.introH ?_ fun $h => ?_; otype; try onorm at $h:ident ⊢))

/-- Instantiate a closed `∀`-theorem at terms with the given typings. -/
macro "ospec " h:term:max hs:(colGt term:max)* : tactic => do
  let mut t ← `(Thm.weak0 $h)
  for x in hs do t ← `(Thm.allE $t $x)
  `(tactic| (have h' := $t; (try onorm at h'); exact h'))

/-- Weaken the hypothesis `h : Thm env Γ₀ P` to the goal's context, which extends `Γ₀`. -/
elab "olift " h:ident : tactic => withMainContext do
  let goal ← getMainGoal
  let_expr Thm env Γ _ := ← instantiateMVars (← goal.getType)
    | throwError "olift: goal is not `Thm env Γ P`"
  let d ← getLocalDeclFromUserName h.getId
  let_expr Thm _ Γ₀ P := ← instantiateMVars d.type
    | throwError "olift: {h} is not `Thm env Γ P`"
  let mut cur := Γ
  let mut pre := #[]
  while !(← isDefEq cur Γ₀) do
    let_expr List.cons _ A rest := cur | throwError "olift: {Γ₀} is not a suffix of {Γ}"
    pre := pre.push A
    cur := rest
  let Δ ← mkListLit (mkConst ``VExpr) pre.toList
  let pf ← mkAppM ``Thm.weakL #[Δ, d.toExpr]
  let ty ← mkAppM ``Thm #[env, Γ, mkApp3 (mkConst ``VExpr.liftN) (toExpr pre.size) P (toExpr 0)]
  let (_, g) ← (← goal.assert d.userName ty (← mkExpectedTypeHint pf ty)).intro1P
  replaceMainGoal [← g.tryClear d.fvarId]
  evalTactic (← `(tactic| try simp only [obj_simp] at $h:ident))

macro "oind" : tactic => `(tactic|
  (refine Thm.ind ?_ ?_ ?_; otype; (try onorm); on_goal 2 => try onorm))

/-- Close the goal by the hypothesis at the first de Bruijn index whose type matches. -/
elab "ohyp" : tactic => do
  for i in List.range 16 do
    let s ← saveState
    try
      Term.withoutErrToSorry <| evalTactic
        (← `(tactic| exact Thm.hyp (i := $(Lean.quote i)) (by olookup)))
      return
    catch _ => s.restore
  throwError "ohyp: no hypothesis matches"

macro "orefl" : tactic => `(tactic| (refine Thm.refl ?_; otype))

/-- Object binders over `Nat` taking their body as the only argument. -/
def isBinder (c : Name) : Bool := c == ``Obj.all || c == `Incomplete.Obj.ex

/-- For `fn` applied to `args` returning an object term or a list of them, which arguments are
object terms or lists of them (`true`) and which are codes or numbers (`false`); `none` if some
argument is neither. Such a function is taken to keep its term arguments at its own depth, so
lifting and instantiation are excluded. -/
def termArgs (fn : Expr) (args : Array Expr) : MetaM (Option (Array Bool)) := do
  if args.isEmpty then return none
  if let .const c _ := fn then
    if c == ``VExpr.liftN || c == ``VExpr.lift || c == ``VExpr.inst || c == ``VExpr.subst then
      return none
  let vexpr := mkConst ``VExpr
  let list := mkApp (mkConst ``List [.zero]) vexpr
  forallTelescopeReducing (← inferType fn) fun xs body => do
    if xs.size != args.size then return none
    unless (← isDefEq body vexpr) || (← isDefEq body list) do return none
    let mut ks := #[]
    for x in xs do
      let t ← inferType x
      if (← isDefEq t vexpr) || (← isDefEq t list) then ks := ks.push true
      else if (← isDefEq t (mkConst `Incomplete.PR)) || (← isDefEq t (mkConst ``Nat)) then
        ks := ks.push false
      else return none
    return some ks

/-- `e` is an instance of the pattern `a` up to reducible unfolding, at which the equations
`conds` among the rule's premises hold by `rfl`; these are then proved. -/
def matchOcc (conds : Array MVarId) (a e : Expr) : MetaM Bool := do
  let st ← saveState
  unless ← withReducible (isDefEq e a) do return false
  for m in conds do
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    let some (_, l, r) := ty.eq? | continue
    if ← isDefEq l r then m.assign (← mkEqRefl l)
    else
      st.restore
      return false
  return true

/-- `e₀` with `e₀.liftN d = e` up to `obj_simp`'s normal form, read off syntactically: `bvar i`
for `i ≥ d`, `d` outer `lift`s, and functions of terms over these; `none` if `e` may mention one
of the `d` innermost variables. -/
partial def unliftN (d : Nat) (e : Expr) : MetaM (Option Expr) := do
  if d == 0 then return some e
  let e ← instantiateMVars e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const c _ =>
    if c == ``VExpr.bvar && args.size == 1 then
      let some i := args[0]!.nat? | return none
      return if i < d then none else some (mkApp (mkConst ``VExpr.bvar) (toExpr (i - d)))
    else if c == ``VExpr.lift && args.size == 1 then unliftN (d - 1) args[0]!
    else if c == ``VExpr.liftN && args.size == 3 then
      let (some n, some 0) := (args[0]!.nat?, args[2]!.nat?) | return none
      if n ≤ d then unliftN (d - n) args[1]!
      else return some (mkApp3 fn (toExpr (n - d)) args[1]! args[2]!)
    else if c == ``VExpr.lam || c == ``VExpr.forallE || isBinder c then return none
    else if c == ``VExpr.sort || c == ``VExpr.const || c == ``List.nil then return some e
    else if c == ``List.cons && args.size == 3 then
      let (some x, some l) := (← unliftN d args[1]!, ← unliftN d args[2]!) | return none
      return some (mkApp3 fn args[0]! x l)
    else
      let some ks ← termArgs fn args | return if e.hasFVar || e.hasMVar then none else some e
      let mut out := #[]
      for (x, k) in args.zip ks do
        if k then
          let some x ← unliftN d x | return none
          out := out.push x
        else out := out.push x
      return some (mkAppN fn out)
  | _ => return none

/-- The motive body `M` with `M.inst a d = e`, abstracting the occurrences of `a`, and under `d`
binders those of `a.liftN d`; `occ` records the first. -/
partial def absMotive (occ : IO.Ref (Option Expr)) (conds : Array MVarId) (a : Expr) (d : Nat)
    (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some e₀ ← unliftN d e then
    if ← matchOcc conds a e₀ then
      if (← occ.get).isNone then occ.set e₀
      return mkApp (mkConst ``VExpr.bvar) (toExpr d)
  let fn := e.getAppFn
  let args := e.getAppArgs
  let liftLeaf : MetaM Expr := do
    if ← isDefEq (← inferType e) (mkApp (mkConst ``List [.zero]) (mkConst ``VExpr)) then
      let f := mkLambda `x .default (mkConst ``VExpr)
        (mkApp3 (mkConst ``VExpr.liftN) (toExpr 1) (.bvar 0) (toExpr d))
      return mkAppN (mkConst ``List.map [.zero, .zero]) #[mkConst ``VExpr, mkConst ``VExpr, f, e]
    return mkApp3 (mkConst ``VExpr.liftN) (toExpr 1) e (toExpr d)
  match fn with
  | .const c _ =>
    if c == ``VExpr.bvar && args.size == 1 then
      match args[0]!.nat? with
      | some i => return mkApp (mkConst ``VExpr.bvar) (toExpr (if i < d then i else i + 1))
      | none => liftLeaf
    else if (c == ``VExpr.lam || c == ``VExpr.forallE) && args.size == 2 then
      return mkApp2 fn (← absMotive occ conds a d args[0]!) (← absMotive occ conds a (d + 1) args[1]!)
    else if isBinder c && args.size == 1 then
      return mkApp fn (← absMotive occ conds a (d + 1) args[0]!)
    else if c == ``VExpr.sort || c == ``VExpr.const || c == ``List.nil then
      return e
    else if c == ``List.cons && args.size == 3 then
      return mkApp3 fn args[0]! (← absMotive occ conds a d args[1]!) (← absMotive occ conds a d args[2]!)
    else
      match ← termArgs fn args with
      | some ks => return mkAppN fn (← (args.zip ks).mapM fun (x, k) =>
          if k then absMotive occ conds a d x else pure x)
      | none => liftLeaf
  | _ => liftLeaf

/-- Rewrite once by `h` the goal `Thm env Γ G`, or the hypothesis `loc : Thm env Γ G`. -/
def orwCore (stx : Term) (symm : Bool) (loc : Option FVarId := none) : TacticM Unit :=
    withMainContext do
  match loc with
  | none => evalTactic (← `(tactic| try simp only [obj_simp]))
  | some x =>
    let n := mkIdent (← x.getUserName)
    evalTactic (← `(tactic| try simp only [obj_simp] at $n:ident))
  let loc ← loc.mapM fun x => do return (← getLocalDeclFromUserName (← x.getUserName)).fvarId
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← match loc with
    | some x => x.getType
    | none => goal.getType)
  let_expr Thm env Γ G := tgt | throwError "orw: not of the form `Thm env Γ P`: {tgt}"
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
  let occ ← IO.mkRef none
  let conds ← mvs.filterMapM fun m => do
    return if (← instantiateMVars (← inferType m)).isEq then some m.mvarId! else none
  let M ← absMotive occ conds a 0 G
  let some a ← occ.get | throwError "orw: no instance of{indentExpr a}\nin{indentExpr G}"
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
  let hEq ← mkExpectedTypeHint hEq (← mkAppM ``Thm #[env, Γ, ← mkAppM ``EqN #[a, b]])
  let hG ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``VExpr.inst #[M, a, toExpr 0]) G)
  let newTy ← mkAppM ``Thm #[env, Γ, ← mkAppM ``VExpr.inst #[M, b, toExpr 0]]
  let rest ← match loc with
    | none =>
      let rest ← mkFreshExprSyntheticOpaqueMVar newTy
      goal.assign (← mkAppM ``Thm.rewrite #[hM, ha, hb, hEq, hG, rest])
      pure rest.mvarId!
    | some x =>
      let hMa ← mkAppM ``Thm.cast #[.fvar x, ← mkEqSymm hG]
      let pf ← mkAppM ``Thm.subst #[hM, hEq, ha, hb, hMa]
      let (_, g) ← (← goal.assert (← x.getUserName) newTy pf).intro1P
      g.tryClear x
  let side := (mvs.toList.filterMap fun m =>
    if m.isMVar then some m.mvarId! else none)
  let mut others := []
  for m in side do
    unless ← m.isAssigned do others := others ++ [m]
  setGoals [hG.mvarId!]
  evalTactic (← `(tactic| first | with_reducible rfl | simp only [obj_simp]))
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
        let st ← saveState
        try evalTactic (← `(tactic| otype))
        catch _ =>
          st.restore
          left := left ++ [m]
  setGoals ([rest] ++ left)
  match loc with
  | none => evalTactic (← `(tactic| try simp only [obj_simp]))
  | some x =>
    let n := mkIdent (← x.getUserName)
    evalTactic (← `(tactic| try simp only [obj_simp] at $n:ident))

syntax "orw " "[" Lean.Parser.Tactic.rwRule,* "]" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| orw [$rs,*] $[at $x]?) => do
    for r in rs.getElems do
      let loc ← x.mapM fun x => withMainContext do return (← getLocalDeclFromUserName x.getId).fvarId
      match r with
      | `(Lean.Parser.Tactic.rwRule| ← $t:term) => orwCore t true loc
      | `(Lean.Parser.Tactic.rwRule| $t:term) => orwCore t false loc
      | _ => throwUnsupportedSyntax
    if x.isNone then evalTactic (← `(tactic| try orefl))

/-! ### Statements with named variables -/

/-- `e` with the free variables `xs` (outermost first) bound by binders around depth `d`. Object
binders are `VExpr.lam`, `VExpr.forallE`, `all` and `ex`; lists of terms are traversed, codes
kept, and every other function of terms is taken to keep its arguments at its own depth. -/
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
    else if isBinder c && args.size == 1 then
      return mkApp fn (← bindVars xs (d + 1) args[0]!)
    else if c == ``List.cons && args.size == 3 then
      return mkApp3 fn args[0]! (← bindVars xs d args[1]!) (← bindVars xs d args[2]!)
    else
      let some ks ← termArgs fn args | throwError "∀ₒ: cannot bind variables in {e}"
      return mkAppN fn (← (args.zip ks).mapM fun (x, k) => if k then bindVars xs d x else pure x)
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
