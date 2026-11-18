import Incomplete.Obj.Logic
import Incomplete.Obj.Arith

/-!
# Object numbers as a commutative semiring

The remaining semiring laws (`mul_add`, `mul_assoc`) and additive cancellation, and then
`ONat env Γ`: the terms of `Nat` in `Γ` up to provable equality. It is a `Lean.Grind`
commutative semiring with cancellation, so `grind` decides its equations, from hypotheses too.
`omk e` is the class of `e` (`0` if `e` is not a term), and `oring [h₁, …]` proves a goal
`Thm env Γ (a =ₒ b)` from equations `hᵢ : Thm env Γ (x =ₒ y)` by reading `add`, `mul`, `S`,
`zero` and `lit n` as the semiring's operations and every other term as an atom.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b c a' b' : VExpr}

theorem mul_add_c : Thm env [] (∀ₒ a b c, mul a (add b c) =ₒ add (mul a b) (mul a c)) := by
  ointro; ointro; oind
  · orw [add_zero, mul_zero, add_zero]
  · ointro ih; orw [add_succ, mul_succ, mul_succ, ih, add_assoc]

theorem mul_add (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) :
    Thm env Γ (mul a (add b c) =ₒ add (mul a b) (mul a c)) := by ospec mul_add_c ha hb hc

theorem mul_assoc_c : Thm env [] (∀ₒ a b c, mul (mul a b) c =ₒ mul a (mul b c)) := by
  ointro; ointro; oind
  · orw [mul_zero, mul_zero, mul_zero]
  · ointro ih; orw [mul_succ, mul_succ, ih, mul_add]

theorem mul_assoc (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) :
    Thm env Γ (mul (mul a b) c =ₒ mul a (mul b c)) := by ospec mul_assoc_c ha hb hc

theorem add_right_cancel_c : Thm env [] (∀ₒ a b c, add a c =ₒ add b c →ₒ a =ₒ b) := by
  ointro; ointro; oind
  · ointro h; orw [add_zero, add_zero] at h; exact h
  · ointro ih; ointro h
    olift ih
    orw [add_succ, add_succ] at h
    exact ih.mp ((succ_inj (by otype) (by otype)).mp h)

theorem add_right_cancel (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h : Thm env Γ (add a c =ₒ add b c)) : Thm env Γ (a =ₒ b) := by
  have h' : Thm env Γ (add a c =ₒ add b c →ₒ a =ₒ b) := by ospec add_right_cancel_c ha hb hc
  exact h'.mp h

theorem add_congr (ha : Tm env Γ a) (hb : Tm env Γ b) (ha' : Tm env Γ a') (hb' : Tm env Γ b')
    (h1 : Thm env Γ (a =ₒ a')) (h2 : Thm env Γ (b =ₒ b')) : Thm env Γ (add a b =ₒ add a' b') := by
  orw [h1, h2]

theorem mul_congr (ha : Tm env Γ a) (hb : Tm env Γ b) (ha' : Tm env Γ a') (hb' : Tm env Γ b')
    (h1 : Thm env Γ (a =ₒ a')) (h2 : Thm env Γ (b =ₒ b')) : Thm env Γ (mul a b =ₒ mul a' b') := by
  orw [h1, h2]

theorem add_lit_one (ha : Tm env Γ a) : Thm env Γ (add a (lit 1) =ₒ S a) := by
  show Thm env Γ (add a (S zero) =ₒ S a); orw [add_succ, add_zero]

end

/-! ### The quotient -/

/-- The terms of `Nat` in `Γ`. -/
def OTm (env : Typing) (Γ : List VExpr) : Type := {e : VExpr // Tm env Γ e}

instance OTm.setoid (env : Typing) [ObjEnv env] (Γ : List VExpr) : Setoid (OTm env Γ) where
  r a b := Thm env Γ (a.1 =ₒ b.1)
  iseqv := ⟨fun a => Thm.refl a.2, fun {a b} h => Thm.symm a.2 b.2 h,
    fun {a b c} h1 h2 => Thm.trans a.2 b.2 c.2 h1 h2⟩

/-- The terms of `Nat` in `Γ` up to provable equality. -/
def ONat (env : Typing) [ObjEnv env] (Γ : List VExpr) : Type := Quotient (OTm.setoid env Γ)

namespace ONat
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

/-- The class of a typed term. -/
def of (e : VExpr) (h : Tm env Γ e) : ONat env Γ := Quotient.mk _ ⟨e, h⟩

theorem of_eq {a b : VExpr} {ha : Tm env Γ a} {hb : Tm env Γ b} :
    of a ha = of b hb ↔ Thm env Γ (a =ₒ b) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem ind {P : ONat env Γ → Prop} (h : ∀ e (he : Tm env Γ e), P (of e he)) (x : ONat env Γ) :
    P x := Quotient.ind (fun a => h a.1 a.2) x

instance : Add (ONat env Γ) where
  add := Quotient.lift₂ (fun a b => of (add a.1 b.1) (addTy a.2 b.2))
    fun a b a' b' h1 h2 => Quotient.sound (add_congr a.2 b.2 a'.2 b'.2 h1 h2)

instance : Mul (ONat env Γ) where
  mul := Quotient.lift₂ (fun a b => of (mul a.1 b.1) (mulTy a.2 b.2))
    fun a b a' b' h1 h2 => Quotient.sound (mul_congr a.2 b.2 a'.2 b'.2 h1 h2)

instance : NatCast (ONat env Γ) where natCast n := of (lit n) (litTy n)
instance (n : Nat) : OfNat (ONat env Γ) n where ofNat := of (lit n) (litTy n)
instance : SMul Nat (ONat env Γ) where smul n x := (n : ONat env Γ) * x

/-- Powers, by recursion on the exponent. -/
def npow (x : ONat env Γ) : Nat → ONat env Γ
  | 0 => 1
  | n + 1 => npow x n * x

instance : HPow (ONat env Γ) Nat (ONat env Γ) where hPow := npow

@[simp] theorem of_add {a b : VExpr} (ha : Tm env Γ a) (hb : Tm env Γ b) :
    of a ha + of b hb = of (add a b) (addTy ha hb) := rfl
@[simp] theorem of_mul {a b : VExpr} (ha : Tm env Γ a) (hb : Tm env Γ b) :
    of a ha * of b hb = of (mul a b) (mulTy ha hb) := rfl
theorem zero_def : (0 : ONat env Γ) = of zero zeroTy := rfl
theorem one_def : (1 : ONat env Γ) = of (lit 1) (litTy 1) := rfl
theorem ofNat_def (n : Nat) : (OfNat.ofNat n : ONat env Γ) = of (lit n) (litTy n) := rfl

theorem mul_comm' : ∀ x y : ONat env Γ, x * y = y * x :=
  ind fun _ ha => ind fun _ hb => of_eq.2 (mul_comm ha hb)
theorem mul_one' : ∀ x : ONat env Γ, x * 1 = x := ind fun a ha => of_eq.2 (by
  show Thm env Γ (mul a (S zero) =ₒ a); orw [mul_succ, mul_zero, zero_add])
theorem zero_mul' : ∀ x : ONat env Γ, 0 * x = 0 := ind fun _ ha => of_eq.2 (zero_mul ha)
theorem left_distrib' : ∀ x y z : ONat env Γ, x * (y + z) = x * y + x * z :=
  ind fun _ ha => ind fun _ hb => ind fun _ hc => of_eq.2 (mul_add ha hb hc)

instance commSemiring : Lean.Grind.CommSemiring (ONat env Γ) where
  add_zero := ind fun _ ha => of_eq.2 (add_zero ha)
  add_comm := ind fun _ ha => ind fun _ hb => of_eq.2 (add_comm ha hb)
  add_assoc := ind fun _ ha => ind fun _ hb => ind fun _ hc => of_eq.2 (add_assoc ha hb hc)
  mul_assoc := ind fun _ ha => ind fun _ hb => ind fun _ hc => of_eq.2 (mul_assoc ha hb hc)
  mul_one := mul_one'
  left_distrib := left_distrib'
  zero_mul := zero_mul'
  mul_comm := mul_comm'
  one_mul x := (mul_comm' 1 x).trans (mul_one' x)
  mul_zero x := (mul_comm' x 0).trans (zero_mul' x)
  right_distrib x y z := by
    rw [mul_comm' (x + y), left_distrib' z x y, mul_comm' z, mul_comm' z]
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := of_eq.2 (by
    show Thm env Γ (S (lit n) =ₒ add (lit n) (S zero)); orw [add_succ, add_zero])

instance : Lean.Grind.AddRightCancel (ONat env Γ) where
  add_right_cancel := ind fun _ ha => ind fun _ hb => ind fun _ hc h =>
    of_eq.2 (add_right_cancel ha hb hc (of_eq.1 h))

end ONat

open Classical in
/-- The class of `e` if it is a term of `Nat` in `Γ`, and `0` otherwise. -/
noncomputable def omk (env : Typing) [ObjEnv env] (Γ : List VExpr) (e : VExpr) : ONat env Γ :=
  if h : Tm env Γ e then ONat.of e h else 0

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b : VExpr}

theorem omk_of (h : Tm env Γ a) : omk env Γ a = ONat.of a h := dif_pos h

theorem omk_add (ha : Tm env Γ a) (hb : Tm env Γ b) :
    omk env Γ (add a b) = omk env Γ a + omk env Γ b := by
  rw [omk_of ha, omk_of hb, omk_of (addTy ha hb)]; rfl
theorem omk_mul (ha : Tm env Γ a) (hb : Tm env Γ b) :
    omk env Γ (mul a b) = omk env Γ a * omk env Γ b := by
  rw [omk_of ha, omk_of hb, omk_of (mulTy ha hb)]; rfl
theorem omk_S (ha : Tm env Γ a) : omk env Γ (S a) = omk env Γ a + 1 := by
  rw [omk_of ha, omk_of (STy ha), ONat.one_def, ONat.of_add]
  exact ONat.of_eq.2 (Thm.symm (addTy ha (litTy 1)) (STy ha) (add_lit_one ha))
theorem omk_zero : omk env Γ zero = 0 := omk_of zeroTy
theorem omk_lit (n : Nat) : omk env Γ (lit n) = (n : ONat env Γ) := omk_of (litTy n)

theorem omk_eq (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a =ₒ b)) :
    omk env Γ a = omk env Γ b := by
  rw [omk_of ha, omk_of hb]; exact ONat.of_eq.2 h

theorem eq_of_omk (ha : Tm env Γ a) (hb : Tm env Γ b) (h : omk env Γ a = omk env Γ b) :
    Thm env Γ (a =ₒ b) := by
  rw [omk_of ha, omk_of hb] at h; exact ONat.of_eq.1 h

end

/-- `oring [h₁, …]` proves `Thm env Γ (a =ₒ b)` by commutative-semiring reasoning from the
equations `hᵢ : Thm env Γ (x =ₒ y)`. -/
syntax "oring" (" [" term,* "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| oring $[[$hs,*]]?) => do
    evalTactic (← `(tactic| try simp only [obj_simp]))
    let Γ ← withMainContext do
      let_expr Thm _ Γ _ := ← instantiateMVars (← getMainTarget)
        | throwError "oring: goal is not `Thm env Γ P`"
      Term.exprToSyntax Γ
    evalTactic (← `(tactic| refine eq_of_omk (Γ := $Γ) (by otype) (by otype) ?_))
    for h in (hs.map (·.getElems)).getD #[] do
      evalTactic (← `(tactic| have h' := $(⟨h⟩)))
      evalTactic (← `(tactic| try simp only [obj_simp] at h'))
      evalTactic (← `(tactic| have := omk_eq (Γ := $Γ) (by otype) (by otype) h'))
      evalTactic (← `(tactic| clear h'))
    evalTactic (← `(tactic| simp (disch := otype) only [omk_add, omk_mul, omk_S, omk_zero, omk_lit] at *))
    evalTactic (← `(tactic| grind))

end Incomplete.Obj
