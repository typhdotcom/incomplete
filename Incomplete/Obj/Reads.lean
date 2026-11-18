import Incomplete.Obj.Bnd
import Incomplete.InstPR

/-!
# Variables read, compositionally

`bnd (comp2 g a b) ≤ m` from bounds on `g`, `a` and `b`, and likewise for `comp3`, `push`,
`succ` and `prec`; `obnd` proves `bnd f ≤ m` for a code composed from `PRLib`'s combinators by
following its structure, never evaluating `bnd` on the whole code.
-/

namespace Incomplete.Obj
open PR

theorem bnd_push_le {h g : PR} {m : Nat} (hh : bnd h ≤ m) (hg : bnd g ≤ m + 1) :
    bnd (push h g) ≤ m := by simp only [bnd]; omega

theorem bnd_succ_le {f : PR} {m : Nat} (h : bnd f ≤ m) : bnd (PR.succ f) ≤ m := h

theorem bnd_var_le {i m : Nat} (h : i < m) : bnd (var i) ≤ m := h

theorem bnd_num_le (n m : Nat) : bnd (num n) ≤ m := by rw [bnd_num]; exact Nat.zero_le _

theorem bnd_comp2_le {g a b : PR} {m : Nat} (hg : bnd g ≤ m + 2) (ha : bnd a ≤ m) (hb : bnd b ≤ m) :
    bnd (comp2 g a b) ≤ m := by
  obtain ⟨σ, e, hσ⟩ : ∃ σ : Nat → Nat, comp2 g a b = push a (push (ren Nat.succ b) (ren σ g)) ∧
      ∀ i, σ i ≤ max i 1 := ⟨_, rfl, fun i => by rcases i with _ | _ | i <;> simp⟩
  have h1 := bnd_ren_le b Nat.succ (m + 1) fun i hi => by omega
  have h2 := bnd_ren_le g σ (m + 2) fun i hi => by have := hσ i; omega
  rw [e]; simp only [bnd]; omega

theorem bnd_comp3_le {g a b c : PR} {m : Nat} (hg : bnd g ≤ m + 3) (ha : bnd a ≤ m)
    (hb : bnd b ≤ m) (hc : bnd c ≤ m) : bnd (comp3 g a b c) ≤ m := by
  obtain ⟨σ, e, hσ⟩ : ∃ σ : Nat → Nat,
      comp3 g a b c = push a (push (ren Nat.succ b) (push (ren (· + 2) c) (ren σ g))) ∧
      ∀ i, σ i ≤ max i 2 := ⟨_, rfl, fun i => by rcases i with _ | _ | _ | i <;> simp⟩
  have h1 := bnd_ren_le b Nat.succ (m + 1) fun i hi => by omega
  have h2 := bnd_ren_le c (· + 2) (m + 2) fun i hi => by omega
  have h3 := bnd_ren_le g σ (m + 3) fun i hi => by have := hσ i; omega
  rw [e]; simp only [bnd]; omega

theorem bnd_prec_le {g h : PR} {m : Nat} (h1 : 1 ≤ m) (hg : bnd g ≤ m - 1) (hh : bnd h ≤ m + 1) :
    bnd (prec g h) ≤ m := by simp only [bnd]; omega

theorem bnd_const_le {f : PR} {m n : Nat} (h : bnd f ≤ n) (hn : n ≤ m := by omega) : bnd f ≤ m :=
  Nat.le_trans h hn

theorem bnd_subC : bnd subC ≤ 2 := by decide
theorem bnd_addC : bnd addC ≤ 2 := by decide
theorem bnd_mulC : bnd mulC ≤ 2 := by decide
theorem bnd_pairC : bnd pairC ≤ 2 := by decide
theorem bnd_selC : bnd selC ≤ 3 := by decide
theorem bnd_triC : bnd triC ≤ 1 := by decide
theorem bnd_triRootC : bnd triRootC ≤ 1 := by decide
theorem bnd_iterC : bnd iterC ≤ 2 := by simp [bnd_simp]
theorem bnd_dmC (k : Nat) : bnd (dmC k) ≤ 1 := by simp [bnd_simp]

open Lean Meta Elab Tactic in
/-- The code `f` of a goal `bnd f ≤ m`. -/
def bndGoal? (t : Expr) : MetaM (Option Expr) := do
  let_expr LE.le _ _ lhs _ := ← instantiateMVars t | return none
  let_expr bnd f := lhs | return none
  return some f

open Lean Meta Elab Tactic in
/-- Prove `bnd f ≤ m` for a code `f` composed by `comp2`, `comp3`, `push` and `succ` from
variables, numerals, the basic codes, and codes bounded by hypotheses. -/
partial def obndCore (g : MVarId) : TacticM Unit := g.withContext do
  let some f ← bndGoal? (← g.getType) | throwError "obnd: not `bnd f ≤ m`"
  let finish (gs : List MVarId) : TacticM Unit := do
    for g' in gs do
      unless ← g'.isAssigned do
        if (← bndGoal? (← g'.getType)).isSome then obndCore g'
        else
          setGoals [g']; evalTactic (← `(tactic| decide))
  let apply (n : Name) : TacticM Unit := do finish (← g.apply (← mkConstWithFreshMVarLevels n))
  let atom (h : Expr) : TacticM Unit := do
    setGoals [g]
    evalTactic (← `(tactic| exact bnd_const_le $(← Term.exprToSyntax h) (by decide)))
  let .const c _ := f.getAppFn | throwError "obnd: no bound for {f}"
  if c == ``comp2 then apply ``bnd_comp2_le
  else if c == ``comp3 then apply ``bnd_comp3_le
  else if c == ``PR.push then apply ``bnd_push_le
  else if c == ``PR.succ then apply ``bnd_succ_le
  else if c == ``PR.var then apply ``bnd_var_le
  else if c == ``PR.num then apply ``bnd_num_le
  else if c == ``PR.zero then apply ``Nat.zero_le
  else if c == ``PR.prec then apply ``bnd_prec_le
  else
    let table := [(``subC, ``bnd_subC), (``addC, ``bnd_addC), (``mulC, ``bnd_mulC),
      (``pairC, ``bnd_pairC), (``selC, ``bnd_selC), (``triC, ``bnd_triC),
      (``triRootC, ``bnd_triRootC), (``iterC, ``bnd_iterC)]
    if let some (_, n) := table.find? (·.1 == c) then atom (mkConst n)
    else if c == ``dmC then atom (mkApp (mkConst ``bnd_dmC) f.appArg!)
    else
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if let some f' ← bndGoal? d.type then
          if f' == f then atom d.toExpr; return
      throwError "obnd: no bound for {f}"

elab "obnd_core" : tactic => do obndCore (← Lean.Elab.Tactic.getMainGoal)

/-- Prove `bnd f ≤ m` for a code `f` composed from `PRLib`'s combinators. -/
macro "obnd" : tactic => `(tactic| (
  simp only [ifz, leq, eqz, cpair, fstC, fstC.sndC, sndC, modC, divC, tagC, histK, keyC, minP, nthC,
    addP, liftP, instP, covPC, histPC, covC, histC]
  obnd_core))

end Incomplete.Obj
