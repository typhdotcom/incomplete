import Incomplete.Obj.Codes

/-!
# Order and truncated subtraction

`a ≤ₒ b` is notation for `a - b = 0`, as `PRLib`'s `leq` tests it, and is equivalent to `∃ c, a + c = b`
(`le_iff_exists`). With the laws of `sub` this characterises the codes `leq` and `eqz`, and
identifies `mulC` with `mul`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- `a ≤ b`, as `a - b = 0`. -/
scoped notation:50 a:51 " ≤ₒ " b:51 => EqN (sub a b) zero

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {a b c x y : VExpr}

/-! ### Multiplication -/

theorem mulC_zero_c : Thm env [] (∀ₒ a, app2 (fn mulC) a zero =ₒ zero) := by
  ointro; orw [mulC_zero]

theorem mulC_succ_c :
    Thm env [] (∀ₒ a b, app2 (fn mulC) a (S b) =ₒ add (app2 (fn mulC) a b) a) := by
  ointro; ointro; orw [mulC_succ, add_comm]

theorem mulC_eq_mul_c : Thm env [] (∀ₒ a b, app2 (fn mulC) a b =ₒ mul a b) := by
  ointro; oind
  · orw [mulC_zero, mul_zero]
  · ointro ih; orw [mulC_succ, mul_succ, ih, add_comm]

theorem mulC_eq_mul (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (app2 (fn mulC) a b =ₒ mul a b) := by ospec mulC_eq_mul_c ha hb

/-! ### Subtraction -/

theorem zero_sub_c : Thm env [] (∀ₒ b, sub zero b =ₒ zero) := by
  oind
  · orw [sub_zero]
  · ointro ih; orw [sub_succ, ih, pred_zero]

theorem zero_sub (hb : Tm env Γ b) : Thm env Γ (sub zero b =ₒ zero) := by ospec zero_sub_c hb

theorem succ_sub_succ_c : Thm env [] (∀ₒ a b, sub (S a) (S b) =ₒ sub a b) := by
  ointro; oind
  · orw [sub_succ, sub_zero, pred_succ, sub_zero]
  · ointro ih; orw [sub_succ, ih, sub_succ]

theorem succ_sub_succ (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (sub (S a) (S b) =ₒ sub a b) := by ospec succ_sub_succ_c ha hb

theorem sub_self_c : Thm env [] (∀ₒ a, sub a a =ₒ zero) := by
  oind
  · orw [sub_zero]
  · ointro ih; orw [succ_sub_succ, ih]

theorem sub_self (ha : Tm env Γ a) : Thm env Γ (sub a a =ₒ zero) := by ospec sub_self_c ha

theorem add_sub_cancel_c : Thm env [] (∀ₒ a b, sub (add a b) b =ₒ a) := by
  ointro; oind
  · orw [add_zero, sub_zero]
  · ointro ih; orw [add_succ, succ_sub_succ, ih]

theorem add_sub_cancel (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (sub (add a b) b =ₒ a) := by ospec add_sub_cancel_c ha hb

theorem sub_add_self_c : Thm env [] (∀ₒ a c, sub a (add a c) =ₒ zero) := by
  ointro; oind
  · orw [add_zero, sub_self]
  · ointro ih; orw [add_succ, sub_succ, ih, pred_zero]

theorem sub_add_self (ha : Tm env Γ a) (hc : Tm env Γ c) :
    Thm env Γ (sub a (add a c) =ₒ zero) := by ospec sub_add_self_c ha hc

/-- `a ≤ b → a + (b - a) = b`. -/
theorem add_sub_of_le_c : Thm env [] (∀ₒ b a, a ≤ₒ b →ₒ add a (sub b a) =ₒ b) := by
  oind
  · ointro; ointro h
    orw [sub_zero] at h
    orw [zero_sub, add_zero, h]
  · ointro ih
    ocases
    · ointro; orw [sub_zero, zero_add]
    · ointro h
      olift ih
      have ih := Thm.allE ih (t := .bvar 1) (by otype)
      onorm at ih
      orw [succ_sub_succ] at h
      orw [succ_sub_succ, succ_add, ih.mp h]

theorem add_sub_of_le (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (add a (sub b a) =ₒ b) := by
  have h' : Thm env Γ (a ≤ₒ b →ₒ add a (sub b a) =ₒ b) := by ospec add_sub_of_le_c hb ha
  exact h'.mp h

theorem le_antisymm (ha : Tm env Γ a) (hb : Tm env Γ b) (h1 : Thm env Γ (a ≤ₒ b))
    (h2 : Thm env Γ (b ≤ₒ a)) : Thm env Γ (a =ₒ b) := by
  have h := add_sub_of_le ha hb h1
  have h2 : Thm env Γ (sub b a =ₒ zero) := h2
  orw [h2, add_zero] at h
  exact h

theorem le_iff_exists_c : Thm env [] (∀ₒ a b, a ≤ₒ b ↔ₒ ∃ₒ c, add a c =ₒ b) := by
  ointro; ointro; osplit
  · ointro h; oexists sub (.bvar 1) (.bvar 2)
    exact add_sub_of_le (by otype) (by otype) h
  · ointro h
    ocases h with hc
    orw [← hc, sub_add_self]

theorem le_iff_exists (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (a ≤ₒ b ↔ₒ ∃ₒ c, add a.lift c =ₒ b.lift) := by ospec le_iff_exists_c ha hb

theorem add_eq_zero_c : Thm env [] (∀ₒ a b, add a b =ₒ zero →ₒ a =ₒ zero ∧ₒ b =ₒ zero) := by
  ointro; ocases
  · ointro h; orw [add_zero] at h; osplit
    · exact h
    · orefl
  · ointro h; orw [add_succ] at h; oexfalso
    exact (succ_ne_zero (by otype)).mp h

theorem add_eq_zero (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (add a b =ₒ zero →ₒ a =ₒ zero ∧ₒ b =ₒ zero) := by ospec add_eq_zero_c ha hb

/-! ### `leq` and `eqz` -/

theorem ev_leq_iff {p q : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (leq p q) l =ₒ zero ↔ₒ ∃ₒ c, add (ev p l).lift c =ₒ (ev q l).lift) := by
  orw [ev_leq rfl]
  simpa only [obj_simp] using le_iff_exists (evTy (f := p) hl) (evTy (f := q) hl)

theorem ev_eqz_self {p : PR} (hl : Tms env Γ l) : Thm env Γ (ev (eqz p p) l =ₒ zero) := by
  orw [ev_eqz rfl, sub_self, add_zero]

theorem ev_eqz_zero {p q : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (eqz p q) l =ₒ zero →ₒ ev p l =ₒ ev q l) := by
  ointro h
  orw [ev_eqz rfl] at h
  have h := (add_eq_zero (by otype) (by otype)).mp h
  ocases h with h1 h2
  exact le_antisymm (by otype) (by otype) h2 h1

end

end Incomplete.Obj
