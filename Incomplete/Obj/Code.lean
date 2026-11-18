import Incomplete.Obj.Arith
import Incomplete.PRLib

/-!
# Primitive recursive codes as atoms

`fn f` is closed for every code `f`, so object-level proofs can mention it for an arbitrary `f`
and reason about it through lemmas, without unfolding it. `add` is literally `fn PR.addC`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

theorem fn_closed (f : PR) : (fn f).ClosedN :=
  (fnT (env := natEnv) f).closedN.1

@[obj_simp] theorem fn_liftN (f : PR) : (fn f).liftN n k = fn f := (fn_closed f).liftN_eq (Nat.zero_le _)
@[obj_simp] theorem fn_inst (f : PR) : (fn f).inst e k = fn f := (fn_closed f).instN_eq (Nat.zero_le _)

theorem fnTy {env : Typing} [E : ObjEnv env] {Γ : List VExpr} (f : PR) :
    env.HasType Γ (fn f) (.forallE nat (.forallE nat nat)) :=
  (fnT f).weak0

macro_rules | `(tactic| otype_rules) => `(tactic| with_reducible exact fnTy _)

/-- `add` is the compiled addition code of `PRLib`, so its lemmas are about `fn PR.addC`. -/
theorem addF_eq_fn : addF = fn PR.addC := rfl

/-- An instance of commutativity at an arbitrary code. -/
theorem fn_add_comm_c {env : Typing} [ObjEnv env] (f : PR) :
    Thm env [] (∀ₒ x y, add (app2 (fn f) x y) x =ₒ add x (app2 (fn f) x y)) := by
  ointro; ointro; orw [add_comm (a := app2 (fn f) (.bvar 1) (.bvar 0))]

end Incomplete.Obj
