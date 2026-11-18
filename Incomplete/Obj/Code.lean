import Incomplete.Obj.Arith
import Incomplete.PRLib

/-!
# Primitive recursive codes as atoms

`fn f` is closed for every code `f`, so object-level proofs can mention it for an arbitrary `f`
and reason about it through lemmas, without unfolding it. `add` is literally `fn PR.addC`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv

theorem fn_closed (f : PR) : (fn f).ClosedN :=
  (fnT hasNat_natEnv natEnv_ordered f).closedN natEnv_ordered trivial

@[obj_simp] theorem fn_liftN (f : PR) : (fn f).liftN n k = fn f := (fn_closed f).liftN_eq (Nat.zero_le _)
@[obj_simp] theorem fn_inst (f : PR) : (fn f).inst e k = fn f := (fn_closed f).instN_eq (Nat.zero_le _)

theorem fnTy {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} (f : PR) :
    env.HasType 0 Γ (fn f) (.forallE nat (.forallE nat nat)) :=
  (fnT E.hasNat E.ordered f).weak0 E.ordered

macro_rules | `(tactic| otype) => `(tactic| exact fnTy _)

/-- `add` is the compiled addition code of `PRLib`, so its lemmas are about `fn PR.addC`. -/
theorem addF_eq_fn : addF = fn PR.addC := rfl

/-- An instance of commutativity at an arbitrary code. -/
theorem fn_add_comm_c {env : VEnv} [ObjEnv env] (f : PR) :
    Thm env [] (∀ₒ x y, add (app2 (fn f) x y) x =ₒ add x (app2 (fn f) x y)) := by
  ointro; ointro; orw [add_comm (a := app2 (fn f) (.bvar 1) (.bvar 0))]

end Incomplete.Obj
