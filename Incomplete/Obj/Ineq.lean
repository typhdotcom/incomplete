import Incomplete.Obj.Order
import Incomplete.Obj.Ring

/-!
# Inequalities

`a <ₒ b` is `S a ≤ₒ b`. A proof of `a ≤ₒ b` is a witness `c` with `a + c = b` (`le_intro`), and
`a ≤ₒ b` gives back the witness `b - a` (`le_elim`), so linear facts reduce to equations that
`oring` proves; `ole c [h₁, …]` does this for a goal `a ≤ₒ b` or `a <ₒ b` at the witness `c`,
reading each `hᵢ : x ≤ₒ y` as `x + (y - x) = y`. On top: reflexivity, transitivity, totality and
trichotomy, antisymmetry, monotonicity and cancellation of `+` and `*`, and the interaction with
truncated subtraction.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- `a < b`, as `S a ≤ b`. -/
scoped notation:50 a:51 " <ₒ " b:51 => EqN (sub (S a) b) zero

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {a b c d k m : VExpr}

theorem le_intro (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h : Thm env Γ (add a c =ₒ b)) : Thm env Γ (a ≤ₒ b) := by
  orw [← h, sub_add_self]

theorem le_elim (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (add a (sub b a) =ₒ b) := add_sub_of_le ha hb h

theorem le_refl (ha : Tm env Γ a) : Thm env Γ (a ≤ₒ a) := sub_self ha

theorem le_of_eq (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a =ₒ b)) :
    Thm env Γ (a ≤ₒ b) := by
  orw [h]; exact le_refl hb

theorem zero_le (ha : Tm env Γ a) : Thm env Γ (zero ≤ₒ a) := zero_sub ha

theorem le_add_right (ha : Tm env Γ a) (hc : Tm env Γ c) : Thm env Γ (a ≤ₒ add a c) :=
  sub_add_self ha hc

theorem le_add_left (ha : Tm env Γ a) (hc : Tm env Γ c) : Thm env Γ (a ≤ₒ add c a) :=
  le_intro ha (addTy hc ha) hc (by oring)

theorem succ_le_succ (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (S a ≤ₒ S b) := by
  orw [succ_sub_succ]; exact h

theorem le_of_succ_le_succ (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (S a ≤ₒ S b)) :
    Thm env Γ (a ≤ₒ b) := by
  orw [succ_sub_succ] at h; exact h

theorem lt_succ_iff (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (a <ₒ S b) = Thm env Γ (a ≤ₒ b) :=
  propext ⟨le_of_succ_le_succ ha hb, succ_le_succ ha hb⟩

theorem le_succ (ha : Tm env Γ a) : Thm env Γ (a ≤ₒ S a) :=
  le_intro ha (STy ha) (litTy 1) (by oring)

theorem lt_succ (ha : Tm env Γ a) : Thm env Γ (a <ₒ S a) := le_refl (STy ha)

theorem le_trans (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) (h1 : Thm env Γ (a ≤ₒ b))
    (h2 : Thm env Γ (b ≤ₒ c)) : Thm env Γ (a ≤ₒ c) :=
  le_intro ha hc (addTy (subTy hb ha) (subTy hc hb)) (by oring [le_elim ha hb h1, le_elim hb hc h2])

theorem le_of_lt (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a <ₒ b)) :
    Thm env Γ (a ≤ₒ b) := le_trans ha (STy ha) hb (le_succ ha) h

theorem lt_of_lt_of_le (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h1 : Thm env Γ (a <ₒ b)) (h2 : Thm env Γ (b ≤ₒ c)) : Thm env Γ (a <ₒ c) :=
  le_trans (STy ha) hb hc h1 h2

theorem lt_of_le_of_lt (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h1 : Thm env Γ (a ≤ₒ b)) (h2 : Thm env Γ (b <ₒ c)) : Thm env Γ (a <ₒ c) :=
  le_trans (STy ha) (STy hb) hc (succ_le_succ ha hb h1) h2

theorem lt_trans (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h1 : Thm env Γ (a <ₒ b)) (h2 : Thm env Γ (b <ₒ c)) : Thm env Γ (a <ₒ c) :=
  lt_of_lt_of_le ha hb hc h1 (le_of_lt hb hc h2)

/-! ### Monotonicity and cancellation -/

theorem add_le_add (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) (hd : Tm env Γ d)
    (h1 : Thm env Γ (a ≤ₒ b)) (h2 : Thm env Γ (c ≤ₒ d)) : Thm env Γ (add a c ≤ₒ add b d) :=
  le_intro (addTy ha hc) (addTy hb hd) (addTy (subTy hb ha) (subTy hd hc))
    (by oring [le_elim ha hb h1, le_elim hc hd h2])

theorem add_le_add_right (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h : Thm env Γ (a ≤ₒ b)) : Thm env Γ (add a c ≤ₒ add b c) :=
  add_le_add ha hb hc hc h (le_refl hc)

theorem add_le_add_left (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h : Thm env Γ (a ≤ₒ b)) : Thm env Γ (add c a ≤ₒ add c b) :=
  add_le_add hc hc ha hb (le_refl hc) h

theorem le_of_add_le_add_right (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h : Thm env Γ (add a c ≤ₒ add b c)) : Thm env Γ (a ≤ₒ b) :=
  le_intro ha hb (subTy (addTy hb hc) (addTy ha hc))
    (by oring [le_elim (addTy ha hc) (addTy hb hc) h])

theorem le_of_add_le_add_left (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c)
    (h : Thm env Γ (add c a ≤ₒ add c b)) : Thm env Γ (a ≤ₒ b) :=
  le_intro ha hb (subTy (addTy hc hb) (addTy hc ha))
    (by oring [le_elim (addTy hc ha) (addTy hc hb) h])

theorem mul_le_mul_left (ha : Tm env Γ a) (hb : Tm env Γ b) (hk : Tm env Γ k)
    (h : Thm env Γ (a ≤ₒ b)) : Thm env Γ (mul k a ≤ₒ mul k b) :=
  le_intro (mulTy hk ha) (mulTy hk hb) (mulTy hk (subTy hb ha)) (by oring [le_elim ha hb h])

theorem mul_le_mul_right (ha : Tm env Γ a) (hb : Tm env Γ b) (hk : Tm env Γ k)
    (h : Thm env Γ (a ≤ₒ b)) : Thm env Γ (mul a k ≤ₒ mul b k) :=
  le_intro (mulTy ha hk) (mulTy hb hk) (mulTy (subTy hb ha) hk) (by oring [le_elim ha hb h])

theorem mul_le_mul (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) (hd : Tm env Γ d)
    (h1 : Thm env Γ (a ≤ₒ b)) (h2 : Thm env Γ (c ≤ₒ d)) : Thm env Γ (mul a c ≤ₒ mul b d) :=
  le_trans (mulTy ha hc) (mulTy hb hc) (mulTy hb hd) (mul_le_mul_right ha hb hc h1)
    (mul_le_mul_left hc hd hb h2)

/-- `a ≤ k * a` for `0 < k`. -/
theorem le_mul_of_pos (ha : Tm env Γ a) (hk : Tm env Γ k) (h : Thm env Γ (zero <ₒ k)) :
    Thm env Γ (a ≤ₒ mul k a) :=
  le_intro ha (mulTy hk ha) (mulTy (subTy hk (STy zeroTy)) ha)
    (by oring [le_elim (STy zeroTy) hk h])

/-! ### Strictness -/

theorem succ_sub_self_c : Thm env [] (∀ₒ a, sub (S a) a =ₒ S zero) := by
  oind
  · orw [sub_zero]
  · ointro ih; orw [succ_sub_succ, ih]

theorem succ_sub_self (ha : Tm env Γ a) : Thm env Γ (sub (S a) a =ₒ S zero) := by
  ospec succ_sub_self_c ha

theorem lt_irrefl (ha : Tm env Γ a) (h : Thm env Γ (a <ₒ a)) : Thm env Γ ⊥ₒ := by
  orw [succ_sub_self] at h
  exact (succ_ne_zero zeroTy).mp h

theorem not_lt_zero (ha : Tm env Γ a) (h : Thm env Γ (a <ₒ zero)) : Thm env Γ ⊥ₒ := by
  orw [sub_zero] at h
  exact (succ_ne_zero ha).mp h

theorem le_zero (ha : Tm env Γ a) (h : Thm env Γ (a ≤ₒ zero)) : Thm env Γ (a =ₒ zero) := by
  orw [sub_zero] at h; exact h

theorem lt_le_false (ha : Tm env Γ a) (hb : Tm env Γ b) (h1 : Thm env Γ (a <ₒ b))
    (h2 : Thm env Γ (b ≤ₒ a)) : Thm env Γ ⊥ₒ :=
  lt_irrefl ha (lt_of_lt_of_le ha hb ha h1 h2)

theorem zero_lt_succ (ha : Tm env Γ a) : Thm env Γ (zero <ₒ S a) :=
  succ_le_succ zeroTy ha (zero_le ha)

/-! ### Totality -/

theorem lt_or_ge_c : Thm env [] (∀ₒ a b, a <ₒ b ∨ₒ b ≤ₒ a) := by
  oind
  · ocases
    · oright; exact zero_le zeroTy
    · oleft; orw [succ_sub_succ]; exact zero_le (by otype)
  · ointro ih
    ocases
    · oright; exact zero_le (by otype)
    · olift ih
      have ih := Thm.allE ih (t := .bvar 0) (by otype)
      onorm at ih
      orw [succ_sub_succ, succ_sub_succ]; exact ih

/-- `a < b ∨ b ≤ a`. -/
theorem lt_or_ge (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (a <ₒ b ∨ₒ b ≤ₒ a) := by
  ospec lt_or_ge_c ha hb

/-- `a ≤ b ∨ b ≤ a`. -/
theorem le_total (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (a ≤ₒ b ∨ₒ b ≤ₒ a) := by
  ocases (lt_or_ge ha hb) with h h
  · oleft; exact le_of_lt (by otype) (by otype) h
  · oright; exact h

theorem eq_or_lt_of_le (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (a =ₒ b ∨ₒ a <ₒ b) := by
  ocases (lt_or_ge ha hb) with h1 h2
  · oright; exact h1
  · oleft; olift h; exact le_antisymm (by otype) (by otype) h h2

/-- `a < b ∨ a = b ∨ b < a`. -/
theorem lt_trichotomy (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (a <ₒ b ∨ₒ a =ₒ b ∨ₒ b <ₒ a) := by
  ocases (lt_or_ge ha hb) with h1 h2
  · oleft; exact h1
  · oright
    ocases (eq_or_lt_of_le (by otype) (by otype) h2) with h3 h4
    · oleft; exact Thm.symm (by otype) (by otype) h3
    · oright; exact h4

theorem lt_of_le_of_ne (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b))
    (hne : Thm env Γ (¬ₒ (a =ₒ b))) : Thm env Γ (a <ₒ b) := by
  ocases (eq_or_lt_of_le ha hb h) with h1 h2
  · oexfalso; olift hne; exact hne.mp h1
  · exact h2

/-! ### Truncated subtraction -/

theorem sub_add_of_le (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (b ≤ₒ a)) :
    Thm env Γ (add (sub a b) b =ₒ a) := by
  oring [le_elim hb ha h]

theorem add_sub_cancel_left (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (sub (add a b) a =ₒ b) := by
  orw [add_comm, add_sub_cancel]

theorem sub_le (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (sub a b ≤ₒ a) := by
  ocases (le_total ha hb) with h1 h2
  · orw [h1]; exact zero_le (by otype)
  · exact le_intro (by otype) (by otype) (by otype) (sub_add_of_le (by otype) (by otype) h2)

theorem lt_of_sub_eq_succ (ha : Tm env Γ a) (hb : Tm env Γ b) (hm : Tm env Γ m)
    (h : Thm env Γ (sub a b =ₒ S m)) : Thm env Γ (b <ₒ a) := by
  ocases (lt_or_ge hb ha) with h1 h2
  · exact h1
  · oexfalso; olift h; orw [h2] at h; exact (zero_ne_succ (by otype)).mp h

theorem add_of_sub_eq_succ (ha : Tm env Γ a) (hb : Tm env Γ b) (hm : Tm env Γ m)
    (h : Thm env Γ (sub a b =ₒ S m)) : Thm env Γ (add b (S m) =ₒ a) := by
  have h' := le_elim hb ha (le_of_lt hb ha (lt_of_sub_eq_succ ha hb hm h))
  orw [h] at h'; exact h'

theorem sub_sub (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) :
    Thm env Γ (sub (sub a b) c =ₒ sub a (add b c)) := by
  have : Thm env [] (∀ₒ a b c, sub (sub a b) c =ₒ sub a (add b c)) := by
    ointro; ointro; oind
    · orw [sub_zero, add_zero]
    · ointro ih; orw [sub_succ, ih, add_succ, sub_succ]
  ospec this ha hb hc

end

/-! ### `ole` -/

/-- `ole c [h₁, …]` proves `a ≤ₒ b` (or `a <ₒ b`) from `a + c = b` (`S a + c = b`), by `oring`
with the equations `hᵢ` and, for each `hᵢ : x ≤ₒ y`, `x + (y - x) = y`. -/
syntax "ole " term:max (" [" term,* "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| ole $c $[[$hs,*]]?) => do
    evalTactic (← `(tactic| try simp only [obj_simp]))
    evalTactic (← `(tactic| refine le_intro (c := $c) (by otype) (by otype) (by otype) ?_))
    let mut hyps : Array Term := #[]
    for h in (hs.map (·.getElems)).getD #[] do
      let h : Term := ⟨h⟩
      let isLe ← withMainContext do
        let ty ← instantiateMVars (← Meta.inferType (← elabTerm h none))
        let_expr Thm _ _ P := ty | return false
        let_expr EqN l r := P | return false
        let_expr Incomplete.zero := r | return false
        let_expr app2 f _ _ := ← Meta.whnfR l | return false
        Meta.isDefEq f (mkApp (mkConst ``fn) (mkConst ``PR.subC))
      hyps := hyps.push h
      if isLe then hyps := hyps.push (← `(le_elim (by otype) (by otype) $h))
    evalTactic (← `(tactic| oring [$hyps,*]))

end Incomplete.Obj
