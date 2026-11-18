import Incomplete.Obj.Order

/-!
# The basic codes' laws, closed

The equations of `Obj.Codes` and `Obj.Order` about `mulC`, `predC`, `subC`, `leq`, `eqz`,
`selC`, `ifz` and `andz`, quantified over their arguments and stated through `fn`: closed
theorems of any `ObjEnv`, and so `Provable natEnv`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b : VExpr}

theorem mulC_succ' (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (app2 (fn mulC) a (S b) =ₒ add (app2 (fn mulC) a b) a) := by
  orw [mulC_succ, add_comm]

theorem pred_zero_c : Thm env [] (pred zero =ₒ zero) := pred_zero
theorem pred_succ_c : Thm env [] (∀ₒ a, pred (S a) =ₒ a) := by ointro; orw [pred_succ]
theorem sub_zero_c : Thm env [] (∀ₒ a, sub a zero =ₒ a) := by ointro; orw [sub_zero]
theorem sub_succ_c : Thm env [] (∀ₒ a b, sub a (S b) =ₒ pred (sub a b)) := by
  ointro; ointro; orw [sub_succ]

variable (p q c : PR)

theorem eqz_self_c : Thm env [] (∀ₒ x y, app2 (fn (eqz p p)) x y =ₒ zero) := by
  ointro; ointro; orw [fn_ev]; exact ev_eqz_self (by otype)

theorem eqz_zero_c :
    Thm env [] (∀ₒ x y, app2 (fn (eqz p q)) x y =ₒ zero →ₒ app2 (fn p) x y =ₒ app2 (fn q) x y) := by
  ointro; ointro; orw [fn_ev, fn_ev, fn_ev]; exact ev_eqz_zero (by otype)

theorem leq_iff_c : Thm env []
    (∀ₒ x y, app2 (fn (leq p q)) x y =ₒ zero ↔ₒ app2 (fn p) x y ≤ₒ app2 (fn q) x y) := by
  ointro; ointro; orw [fn_ev, ev_leq rfl, fn_ev (f := p), fn_ev (f := q)]
  osplit <;> (ointro h; ohyp)

theorem selC_zero_c : Thm env [] (∀ₒ a b, ev selC [zero, a, b] =ₒ a) := by
  ointro; ointro; orw [ev_selC_zero]

theorem selC_succ_c : Thm env [] (∀ₒ n a b, ev selC [S n, a, b] =ₒ b) := by
  ointro; ointro; ointro; orw [ev_selC_succ]

theorem ifz_zero_c : Thm env []
    (∀ₒ x y, app2 (fn c) x y =ₒ zero →ₒ app2 (fn (ifz c p q)) x y =ₒ app2 (fn p) x y) := by
  ointro; ointro; ointro h
  orw [fn_ev] at h
  orw [fn_ev, fn_ev, ev_ifz_zero rfl (by otype) h]

theorem ifz_succ_c : Thm env []
    (∀ₒ x y n, app2 (fn c) x y =ₒ S n →ₒ app2 (fn (ifz c p q)) x y =ₒ app2 (fn q) x y) := by
  ointro; ointro; ointro; ointro h
  orw [fn_ev] at h
  orw [fn_ev, fn_ev, ev_ifz_succ rfl (by otype) (by otype) h]

theorem andz_zero_c : Thm env [] (∀ₒ x y, app2 (fn p) x y =ₒ zero →ₒ app2 (fn q) x y =ₒ zero →ₒ
    app2 (fn (andz p q)) x y =ₒ zero) := by
  ointro; ointro; ointro h1; ointro h2
  olift h1
  orw [fn_ev] at h1; orw [fn_ev] at h2
  orw [fn_ev, ev_andz_zero rfl (by otype) h1 h2]

theorem andz_left_c : Thm env []
    (∀ₒ x y n, app2 (fn p) x y =ₒ S n →ₒ app2 (fn (andz p q)) x y =ₒ lit 1) := by
  ointro; ointro; ointro; ointro h
  orw [fn_ev] at h
  orw [fn_ev, ev_andz_left rfl (by otype) (by otype) h]

theorem andz_right_c : Thm env [] (∀ₒ x y n, app2 (fn p) x y =ₒ zero →ₒ app2 (fn q) x y =ₒ S n →ₒ
    app2 (fn (andz p q)) x y =ₒ lit 1) := by
  ointro; ointro; ointro; ointro h1; ointro h2
  olift h1
  orw [fn_ev] at h1; orw [fn_ev] at h2
  orw [fn_ev, ev_andz_right rfl (by otype) (by otype) h1 h2]

end

/-! ### In `natEnv` -/

section
open PR

theorem mulC_zero_provable : Provable natEnv (∀ₒ a, app2 (fn mulC) a zero =ₒ zero) := Thm.provable mulC_zero_c
theorem mulC_succ_provable :
    Provable natEnv (∀ₒ a b, app2 (fn mulC) a (S b) =ₒ add (app2 (fn mulC) a b) a) := Thm.provable mulC_succ_c
theorem mulC_eq_mul_provable : Provable natEnv (∀ₒ a b, app2 (fn mulC) a b =ₒ mul a b) :=
  Thm.provable mulC_eq_mul_c

theorem pred_zero_provable : Provable natEnv (pred zero =ₒ zero) := Thm.provable pred_zero_c
theorem pred_succ_provable : Provable natEnv (∀ₒ a, pred (S a) =ₒ a) := Thm.provable pred_succ_c
theorem sub_zero_provable : Provable natEnv (∀ₒ a, sub a zero =ₒ a) := Thm.provable sub_zero_c
theorem sub_succ_provable : Provable natEnv (∀ₒ a b, sub a (S b) =ₒ pred (sub a b)) := Thm.provable sub_succ_c
theorem add_sub_cancel_provable : Provable natEnv (∀ₒ a b, sub (add a b) b =ₒ a) :=
  Thm.provable add_sub_cancel_c
theorem sub_self_provable : Provable natEnv (∀ₒ a, sub a a =ₒ zero) := Thm.provable sub_self_c
theorem le_iff_exists_provable : Provable natEnv (∀ₒ a b, a ≤ₒ b ↔ₒ ∃ₒ c, add a c =ₒ b) :=
  Thm.provable le_iff_exists_c

theorem eqz_self_provable (p : PR) :
    Provable natEnv (∀ₒ x y, app2 (fn (eqz p p)) x y =ₒ zero) := Thm.provable (eqz_self_c p)
theorem eqz_zero_provable (p q : PR) : Provable natEnv
    (∀ₒ x y, app2 (fn (eqz p q)) x y =ₒ zero →ₒ app2 (fn p) x y =ₒ app2 (fn q) x y) :=
  Thm.provable (eqz_zero_c p q)
theorem leq_iff_provable (p q : PR) : Provable natEnv
    (∀ₒ x y, app2 (fn (leq p q)) x y =ₒ zero ↔ₒ app2 (fn p) x y ≤ₒ app2 (fn q) x y) :=
  Thm.provable (leq_iff_c p q)

theorem selC_zero_provable : Provable natEnv (∀ₒ a b, ev selC [zero, a, b] =ₒ a) := Thm.provable selC_zero_c
theorem selC_succ_provable : Provable natEnv (∀ₒ n a b, ev selC [S n, a, b] =ₒ b) := Thm.provable selC_succ_c
theorem ifz_zero_provable (c p q : PR) : Provable natEnv
    (∀ₒ x y, app2 (fn c) x y =ₒ zero →ₒ app2 (fn (ifz c p q)) x y =ₒ app2 (fn p) x y) :=
  Thm.provable (ifz_zero_c p q c)
theorem ifz_succ_provable (c p q : PR) : Provable natEnv
    (∀ₒ x y n, app2 (fn c) x y =ₒ S n →ₒ app2 (fn (ifz c p q)) x y =ₒ app2 (fn q) x y) :=
  Thm.provable (ifz_succ_c p q c)
theorem andz_zero_provable (p q : PR) : Provable natEnv (∀ₒ x y, app2 (fn p) x y =ₒ zero →ₒ
    app2 (fn q) x y =ₒ zero →ₒ app2 (fn (andz p q)) x y =ₒ zero) := Thm.provable (andz_zero_c p q)
theorem andz_left_provable (p q : PR) : Provable natEnv
    (∀ₒ x y n, app2 (fn p) x y =ₒ S n →ₒ app2 (fn (andz p q)) x y =ₒ lit 1) := Thm.provable (andz_left_c p q)
theorem andz_right_provable (p q : PR) : Provable natEnv (∀ₒ x y n, app2 (fn p) x y =ₒ zero →ₒ
    app2 (fn q) x y =ₒ S n →ₒ app2 (fn (andz p q)) x y =ₒ lit 1) := Thm.provable (andz_right_c p q)

end

end Incomplete.Obj
