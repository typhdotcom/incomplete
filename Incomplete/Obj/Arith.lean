import Incomplete.Obj.Rec

/-!
# Addition and multiplication in the object theory

`add` and `mul` are `rec2` functions, recursing on the second argument. Each equation is proved
once as a closed `∀`-theorem (`*_c`) and once schematically, at arbitrary terms in an arbitrary
context, by instantiating it.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

def addF : VExpr := rec2 (.bvar 0) (S (.bvar 0))
def add (a b : VExpr) : VExpr := app2 addF a b
def mulF : VExpr := rec2 zero (add (.bvar 0) (.bvar 2))
def mul (a b : VExpr) : VExpr := app2 mulF a b

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b c : VExpr}

theorem addFTy : env.HasType Γ addF (.forallE nat (.forallE nat nat)) :=
  rec2Ty (.bvar .zero) (STy (.bvar .zero))
theorem addTy (ha : Tm env Γ a) (hb : Tm env Γ b) : Tm env Γ (add a b) := app2Ty addFTy ha hb
theorem mulFTy : env.HasType Γ mulF (.forallE nat (.forallE nat nat)) :=
  rec2Ty zeroTy (addTy (.bvar .zero) (.bvar (.succ (.succ .zero))))
theorem mulTy (ha : Tm env Γ a) (hb : Tm env Γ b) : Tm env Γ (mul a b) := app2Ty mulFTy ha hb

end

theorem addF_closed : addF.ClosedN := (addFTy (env := natEnv) (Γ := [])).closedN.1
theorem mulF_closed : mulF.ClosedN := (mulFTy (env := natEnv) (Γ := [])).closedN.1

section
variable {a b e : VExpr} {n k : Nat}
@[obj_simp] theorem add_liftN : (add a b).liftN n k = add (a.liftN n k) (b.liftN n k) := by
  simp [add, app2, VExpr.liftN, addF_closed.liftN_eq (Nat.zero_le _)]
@[obj_simp] theorem add_inst : (add a b).inst e k = add (a.inst e k) (b.inst e k) := by
  simp [add, app2, VExpr.inst, addF_closed.instN_eq (Nat.zero_le _)]
@[obj_simp] theorem mul_liftN : (mul a b).liftN n k = mul (a.liftN n k) (b.liftN n k) := by
  simp [mul, app2, VExpr.liftN, mulF_closed.liftN_eq (Nat.zero_le _)]
@[obj_simp] theorem mul_inst : (mul a b).inst e k = mul (a.inst e k) (b.inst e k) := by
  simp [mul, app2, VExpr.inst, mulF_closed.instN_eq (Nat.zero_le _)]
end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine addTy ?_ ?_) <;> otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine mulTy ?_ ?_) <;> otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b c : VExpr}

/-! ### Defining equations -/

theorem add_zero_c : Thm env [] (∀ₒ a, add a zero =ₒ a) := by
  ointro
  have := Thm.ofDefEq (rec2_zero (Γ := [nat]) (.bvar .zero) (STy (.bvar .zero)) (.bvar .zero)
    (env := env))
  onorm at this; exact this

theorem add_succ_c : Thm env [] (∀ₒ a b, add a (S b) =ₒ S (add a b)) := by
  ointro; ointro
  have := Thm.ofDefEq (rec2_succ (Γ := [nat, nat]) (.bvar .zero) (STy (.bvar .zero))
    (.bvar (.succ .zero)) (.bvar .zero) (env := env))
  onorm at this; exact this

theorem add_zero (ha : Tm env Γ a) : Thm env Γ (EqN (add a zero) a) := by ospec add_zero_c ha
theorem add_succ (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (EqN (add a (S b)) (S (add a b))) := by ospec add_succ_c ha hb

theorem mul_zero_c : Thm env [] (∀ₒ a, mul a zero =ₒ zero) := by
  ointro
  have := Thm.ofDefEq (rec2_zero (Γ := [nat]) zeroTy
    (addTy (.bvar .zero) (.bvar (.succ (.succ .zero)))) (.bvar .zero) (env := env))
  onorm at this; exact this

theorem mul_succ_c : Thm env [] (∀ₒ a b, mul a (S b) =ₒ add (mul a b) a) := by
  ointro; ointro
  have := Thm.ofDefEq (rec2_succ (Γ := [nat, nat]) zeroTy
    (addTy (.bvar .zero) (.bvar (.succ (.succ .zero)))) (.bvar (.succ .zero)) (.bvar .zero) (env := env))
  onorm at this; exact this

theorem mul_zero (ha : Tm env Γ a) : Thm env Γ (EqN (mul a zero) zero) := by ospec mul_zero_c ha
theorem mul_succ (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (EqN (mul a (S b)) (add (mul a b) a)) := by ospec mul_succ_c ha hb

/-! ### Addition -/

theorem zero_add_c : Thm env [] (∀ₒ a, add zero a =ₒ a) := by
  oind
  · orw [add_zero]
  · ointro ih; orw [add_succ, ih]

theorem zero_add (ha : Tm env Γ a) : Thm env Γ (EqN (add zero a) a) := by ospec zero_add_c ha

theorem succ_add_c : Thm env [] (∀ₒ a b, add (S a) b =ₒ S (add a b)) := by
  ointro; oind
  · orw [add_zero, add_zero]
  · ointro ih; orw [add_succ, add_succ, ih]

theorem succ_add (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (EqN (add (S a) b) (S (add a b))) := by ospec succ_add_c ha hb

theorem add_comm_c : Thm env [] (∀ₒ a b, add a b =ₒ add b a) := by
  ointro; oind
  · orw [add_zero, zero_add]
  · ointro ih; orw [add_succ, succ_add, ih]

theorem add_comm (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (EqN (add a b) (add b a)) := by
  ospec add_comm_c ha hb

theorem add_assoc_c : Thm env [] (∀ₒ a b c, add (add a b) c =ₒ add a (add b c)) := by
  ointro; ointro; oind
  · orw [add_zero, add_zero]
  · ointro ih; orw [add_succ, add_succ, add_succ, ih]

theorem add_assoc (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) :
    Thm env Γ (EqN (add (add a b) c) (add a (add b c))) := by ospec add_assoc_c ha hb hc

/-! ### Multiplication -/

theorem zero_mul_c : Thm env [] (∀ₒ a, mul zero a =ₒ zero) := by
  oind
  · orw [mul_zero]
  · ointro ih; orw [mul_succ, add_zero, ih]

theorem zero_mul (ha : Tm env Γ a) : Thm env Γ (EqN (mul zero a) zero) := by ospec zero_mul_c ha

theorem succ_mul_c : Thm env [] (∀ₒ a b, mul (S a) b =ₒ add (mul a b) b) := by
  ointro; oind
  · orw [mul_zero, mul_zero, add_zero]
  · ointro ih
    orw [mul_succ, mul_succ, ih, add_succ, add_succ, add_assoc, add_assoc,
      add_comm (a := .bvar 1) (b := .bvar 2)]

theorem succ_mul (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (EqN (mul (S a) b) (add (mul a b) b)) := by ospec succ_mul_c ha hb

theorem mul_comm_c : Thm env [] (∀ₒ a b, mul a b =ₒ mul b a) := by
  ointro; oind
  · orw [mul_zero, zero_mul]
  · ointro ih; orw [mul_succ, succ_mul, ih]

theorem mul_comm (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (EqN (mul a b) (mul b a)) := by
  ospec mul_comm_c ha hb

end

/-! ### In `natEnv`, and at arbitrary terms -/

theorem add_comm_provable : Provable natEnv (∀ₒ a b, add a b =ₒ add b a) := Thm.provable add_comm_c
theorem add_assoc_provable :
    Provable natEnv (∀ₒ a b c, add (add a b) c =ₒ add a (add b c)) := Thm.provable add_assoc_c
theorem mul_comm_provable : Provable natEnv (∀ₒ a b, mul a b =ₒ mul b a) := Thm.provable mul_comm_c

/-- Commutativity at any terms `s t : Nat` in any context, over any environment with `Nat`. -/
theorem add_comm_schematic {env : VEnv} (H : HasNat env) (henv : env.Ordered) {Γ : List VExpr}
    {s t : VExpr} (hs : env.HasType 0 Γ s nat) (ht : env.HasType 0 Γ t nat) :
    ∃ p, env.HasType 0 Γ p (EqN (add s t) (add t s)) :=
  have : ObjEnv env := .full H henv
  add_comm (env := env) hs ht

end Incomplete.Obj
