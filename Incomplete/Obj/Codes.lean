import Incomplete.Obj.Eval
import Incomplete.CertPR

/-!
# The basic `PRLib` codes

Their defining equations at symbolic arguments, from the rules of `Obj.Eval`: multiplication
`mulC`, predecessor `predC` (`pred`), truncated subtraction `subC` (`sub a b` is `a - b`), and the
combinators `leq`, `eqz`, `selC`, `ifz` and `andz` on codes. `fn f x y` reads `y` as variable `0`
and `x` as variable `1`, so `sub a b` is `fn subC b a`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- `a - 1`. -/
abbrev pred (a : VExpr) : VExpr := app2 (fn predC) zero a

/-- `a - b`, truncated. -/
abbrev sub (a b : VExpr) : VExpr := app2 (fn subC) b a

/-- The recursion inside `subC`: `subG` at `[b, a]` is `a - b`. -/
def subG : PR := prec (var 0) (push (var 0) predC)

theorem subC_eq : subC = comp2 subG (var 1) (var 0) := rfl

section
variable {a b e : VExpr} {n k : Nat}

@[obj_simp] theorem fn_addC : app2 (fn addC) a b = add a b := rfl
@[obj_simp] theorem fn_predC : app2 (fn predC) zero a = pred a := rfl
@[obj_simp] theorem fn_subC : app2 (fn subC) b a = sub a b := rfl
@[obj_simp] theorem pred_liftN : (pred a).liftN n k = pred (a.liftN n k) := rfl
@[obj_simp] theorem pred_inst : (pred a).inst e k = pred (a.inst e k) := by simp [obj_simp]
@[obj_simp] theorem sub_liftN : (sub a b).liftN n k = sub (a.liftN n k) (b.liftN n k) := by
  simp [obj_simp]
@[obj_simp] theorem sub_inst : (sub a b).inst e k = sub (a.inst e k) (b.inst e k) := by
  simp [obj_simp]

end

attribute [obj_simp] ev_num

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {a b c n : VExpr} {f g h : PR}

theorem predTy' (ha : Tm env Γ a) : Tm env Γ (pred a) := app2Ty (fnTy _) zeroTy ha
theorem subTy (ha : Tm env Γ a) (hb : Tm env Γ b) : Tm env Γ (sub a b) := app2Ty (fnTy _) hb ha

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine predTy' ?_); otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine subTy ?_ ?_) <;> otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {a b c n : VExpr} {f g h : PR}

/-! ### Multiplication -/

theorem mulC_zero (ha : Tm env Γ a) : Thm env Γ (app2 (fn mulC) a zero =ₒ zero) := by
  orw [fn_ev, ev_prec_zero]

theorem mulC_succ (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (app2 (fn mulC) a (S b) =ₒ add a (app2 (fn mulC) a b)) := by
  orw [fn_ev, ev_prec_succ, ev_comp2, ev_fn2, ← fn_ev]

/-! ### Predecessor and subtraction -/

theorem pred_zero : Thm env Γ (pred zero =ₒ zero) := by orw [fn_ev, ev_prec_zero]

theorem pred_succ (ha : Tm env Γ a) : Thm env Γ (pred (S a) =ₒ a) := by
  orw [fn_ev, ev_prec_succ]

theorem sub_fn (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (sub a b =ₒ app2 (fn subG) a b) := by
  orw [fn_ev (f := subC), ev_comp2, ev_fn2]

theorem sub_zero (ha : Tm env Γ a) : Thm env Γ (sub a zero =ₒ a) := by
  orw [sub_fn, fn_ev, ev_prec_zero]

theorem sub_succ (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (sub a (S b) =ₒ pred (sub a b)) := by
  orw [sub_fn, fn_ev (f := subG), ev_prec_succ, ev_push, ev_fn1, ev_fn2, sub_fn]

/-! ### Combinators on codes -/

theorem ev_leq {a b : PR} (hf : f = leq a b) (hl : Tms env Γ l) :
    Thm env Γ (ev f l =ₒ sub (ev a l) (ev b l)) := by
  subst hf; orw [ev_comp2, ev_fn2]

theorem ev_eqz {a b : PR} (hf : f = eqz a b) (hl : Tms env Γ l) :
    Thm env Γ (ev f l =ₒ add (sub (ev b l) (ev a l)) (sub (ev a l) (ev b l))) := by
  subst hf; orw [ev_comp2, ev_fn2, ev_leq rfl, ev_leq rfl]

theorem ev_selC_zero (ha : Tm env Γ a) (hl : Tms env Γ l) :
    Thm env Γ (ev selC (zero :: a :: l) =ₒ a) := by
  orw [ev_prec_zero]

theorem ev_selC_succ (hn : Tm env Γ n) (ha : Tm env Γ a) (hb : Tm env Γ b) (hl : Tms env Γ l) :
    Thm env Γ (ev selC (S n :: a :: b :: l) =ₒ b) := by
  orw [ev_prec_succ]

theorem ev_ifz {c a b : PR} (hf : f = ifz c a b) (hl : Tms env Γ l) :
    Thm env Γ (ev f l =ₒ ev selC (ev c l :: ev a l :: ev b l :: l)) := by
  subst hf; orw [ev_comp3]

theorem ev_ifz_zero {c a b : PR} (hf : f = ifz c a b) (hl : Tms env Γ l)
    (hc : Thm env Γ (ev c l =ₒ zero)) : Thm env Γ (ev f l =ₒ ev a l) := by
  orw [ev_ifz hf, hc, ev_selC_zero]

theorem ev_ifz_succ {c a b : PR} (hf : f = ifz c a b) (hl : Tms env Γ l) (hn : Tm env Γ n)
    (hc : Thm env Γ (ev c l =ₒ S n)) : Thm env Γ (ev f l =ₒ ev b l) := by
  orw [ev_ifz hf, hc, ev_selC_succ]

theorem ev_andz_zero {a b : PR} (hf : f = andz a b) (hl : Tms env Γ l)
    (ha : Thm env Γ (ev a l =ₒ zero)) (hb : Thm env Γ (ev b l =ₒ zero)) :
    Thm env Γ (ev f l =ₒ zero) := by
  orw [ev_ifz_zero hf hl ha, ev_ifz_zero rfl hl hb]

theorem ev_andz_left {a b : PR} (hf : f = andz a b) (hl : Tms env Γ l) (hn : Tm env Γ n)
    (ha : Thm env Γ (ev a l =ₒ S n)) : Thm env Γ (ev f l =ₒ lit 1) := by
  orw [ev_ifz_succ hf hl hn ha]

theorem ev_andz_right {a b : PR} (hf : f = andz a b) (hl : Tms env Γ l) (hn : Tm env Γ n)
    (ha : Thm env Γ (ev a l =ₒ zero)) (hb : Thm env Γ (ev b l =ₒ S n)) :
    Thm env Γ (ev f l =ₒ lit 1) := by
  orw [ev_ifz_zero hf hl ha, ev_ifz_succ rfl hl hn hb]

end

end Incomplete.Obj
