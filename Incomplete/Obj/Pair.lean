import Incomplete.Obj.Ineq

/-!
# Triangular numbers and pairing

The codes `triC`, `triRootC` and `pairC` of `PRLib`, and the combinators `fstC`, `sndC` and
`cpair`, at symbolic arguments: `tri (S n) = tri n + S n` and monotonicity; `triRoot n` is the
largest `s` with `tri s ≤ n`, so `triRoot (tri w + j) = w` for `j ≤ w`; and `fst` and `snd`
invert `pair`, whose value bounds both components.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing
open PR (triC triRootC pairC fstC sndC cpair selC)

/-- `tri a`, the code `triC` at `a`. -/
abbrev tri (a : VExpr) : VExpr := app2 (fn triC) zero a

/-- `triRoot a`, the code `triRootC` at `a`. -/
abbrev triRoot (a : VExpr) : VExpr := app2 (fn triRootC) zero a

/-- `pair a b`, the code `pairC` with `a` in variable `0` and `b` in variable `1`. -/
abbrev pair (a b : VExpr) : VExpr := app2 (fn pairC) b a

/-- The first component of `a`, the code `fstC (var 0)` at `a`. -/
abbrev fst (a : VExpr) : VExpr := app2 (fn (fstC (.var 0))) zero a

/-- The second component of `a`, the code `sndC (var 0)` at `a`. -/
abbrev snd (a : VExpr) : VExpr := app2 (fn (sndC (.var 0))) zero a

section
variable {env : Typing} [E : ObjEnv env] {Γ l : List VExpr} {a b c j n r s w : VExpr} {p q : PR}

/-! ### `triC` -/

theorem tri_zero : Thm env Γ (tri zero =ₒ zero) := by orw [fn_ev, ev_prec_zero]

theorem tri_succ' (ha : Tm env Γ a) : Thm env Γ (tri (S a) =ₒ add (S a) (tri a)) := by
  orw [fn_ev, ev_prec_succ, ev_comp2, ev_fn2, ← fn_ev]

theorem tri_succ (ha : Tm env Γ a) : Thm env Γ (tri (S a) =ₒ add (tri a) (S a)) := by
  orw [tri_succ' ha, add_comm]

theorem le_tri_c : Thm env [] (∀ₒ a, a ≤ₒ tri a) := by
  oind
  · orw [tri_zero]; exact zero_le zeroTy
  · ointro ih
    orw [tri_succ]
    exact le_trans (by otype) (by otype) (by otype) (le_refl (by otype)) (le_add_left (by otype) (by otype))

theorem le_tri (ha : Tm env Γ a) : Thm env Γ (a ≤ₒ tri a) := by ospec le_tri_c ha

theorem tri_le_add_c : Thm env [] (∀ₒ a c, tri a ≤ₒ tri (add a c)) := by
  ointro; oind
  · orw [add_zero]; exact le_refl (by otype)
  · ointro ih
    orw [add_succ, tri_succ]
    exact le_trans (by otype) (by otype) (by otype) ih (le_add_right (by otype) (by otype))

theorem tri_mono (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (tri a ≤ₒ tri b) := by
  have h1 : Thm env Γ (tri a ≤ₒ tri (add a (sub b a))) := by ospec tri_le_add_c ha (subTy hb ha)
  orw [le_elim ha hb h] at h1; exact h1

/-! ### `triRootC` -/

theorem triRoot_zero : Thm env Γ (triRoot zero =ₒ zero) := by orw [fn_ev, ev_prec_zero]

theorem triRoot_succ (hn : Tm env Γ n) : Thm env Γ (triRoot (S n) =ₒ
    ev selC [sub (tri (S (triRoot n))) (S n), S (triRoot n), triRoot n, n, zero]) := by
  orw [fn_ev, ev_prec_succ, ev_ifz rfl, ev_leq rfl, ev_push, ev_fn1 (f := triC), ← fn_ev]

theorem triRoot_succ_of_le (hn : Tm env Γ n) (h : Thm env Γ (tri (S (triRoot n)) ≤ₒ S n)) :
    Thm env Γ (triRoot (S n) =ₒ S (triRoot n)) := by
  orw [triRoot_succ hn, h, ev_selC_zero]

theorem triRoot_succ_of_lt (hn : Tm env Γ n) (hm : Tm env Γ c)
    (h : Thm env Γ (sub (tri (S (triRoot n))) (S n) =ₒ S c)) :
    Thm env Γ (triRoot (S n) =ₒ triRoot n) := by
  orw [triRoot_succ hn, h, ev_selC_succ]

theorem triRoot_spec_succ (hn : Tm env Γ n)
    (h : Thm env Γ (tri (triRoot n) ≤ₒ n ∧ₒ n <ₒ tri (S (triRoot n)))) :
    Thm env Γ (tri (triRoot (S n)) ≤ₒ S n ∧ₒ S n <ₒ tri (S (triRoot (S n)))) := by
  ocases h with h1 h2
  ocases (zero_or_succ (n := sub (tri (S (triRoot n))) (S n)) (by otype)) with hz hs
  · orw [triRoot_succ_of_le (by otype) hz]
    olift h2
    osplit
    · exact hz
    · orw [tri_succ (a := S (triRoot n.lift))]
      ole (add (S (triRoot n.lift)) (sub (tri (S (triRoot n.lift))) (S n.lift))) [h2]
  · ocases hs with hm
    orw [triRoot_succ_of_lt (by otype) (by otype) hm]
    olift h1
    osplit
    · exact le_trans (by otype) (by otype) (by otype) h1 (le_succ (by otype))
    · exact lt_of_sub_eq_succ (by otype) (by otype) (by otype) hm

/-- `tri (triRoot n) ≤ n < tri (triRoot n + 1)`. -/
theorem triRoot_spec_c : Thm env [] (∀ₒ n, tri (triRoot n) ≤ₒ n ∧ₒ n <ₒ tri (S (triRoot n))) := by
  oind
  · orw [triRoot_zero, tri_zero]
    osplit
    · exact le_refl zeroTy
    · orw [tri_succ, tri_zero]; exact le_of_eq (by otype) (by otype) (by oring)
  · ointro ih; exact triRoot_spec_succ (by otype) ih

theorem triRoot_spec (hn : Tm env Γ n) :
    Thm env Γ (tri (triRoot n) ≤ₒ n ∧ₒ n <ₒ tri (S (triRoot n))) := by ospec triRoot_spec_c hn

theorem triRoot_eq (hn : Tm env Γ n) (hs : Tm env Γ s) (h1 : Thm env Γ (tri s ≤ₒ n))
    (h2 : Thm env Γ (n <ₒ tri (S s))) : Thm env Γ (triRoot n =ₒ s) := by
  ocases (triRoot_spec hn) with k1 k2
  ocases (lt_trichotomy (a := triRoot n) (b := s) (by otype) hs) with l1 l23
  · oexfalso; olift h1; olift k2
    exact lt_le_false (by otype) (by otype) k2
      (le_trans (by otype) (by otype) (by otype) (tri_mono (by otype) (by otype) l1) h1)
  · ocases l23 with e l3
    · exact e
    · oexfalso; olift h2; olift k1
      exact lt_le_false (by otype) (by otype) h2
        (le_trans (by otype) (by otype) (by otype) (tri_mono (by otype) (by otype) l3) k1)

theorem triRoot_tri_add (hw : Tm env Γ w) (hj : Tm env Γ j) (h : Thm env Γ (j ≤ₒ w)) :
    Thm env Γ (triRoot (add (tri w) j) =ₒ w) := by
  refine triRoot_eq (by otype) hw (le_add_right (by otype) hj) ?_
  orw [tri_succ hw]
  ole (sub w j) [h]

/-! ### `pairC`, `fstC`, `sndC` -/

theorem pair_eq (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (pair a b =ₒ add (tri (add a b)) b) := by
  orw [fn_ev, ev_comp2, ev_fn2 (f := PR.addC), ev_push, ev_fn1 (f := triC),
    ev_fn2 (f := PR.addC), add_comm (a := b) (b := a), add_comm (a := b)]

theorem ev_cpair (hl : Tms env Γ l) : Thm env Γ (ev (cpair p q) l =ₒ pair (ev p l) (ev q l)) := by
  orw [ev_comp2, ev_fn2 (f := pairC)]

theorem ev_sndC' (hl : Tms env Γ l) :
    Thm env Γ (ev (sndC p) l =ₒ sub (ev p l) (tri (triRoot (ev p l)))) := by
  orw [ev_comp2, ev_fn2 (f := PR.subC), ev_push, ev_fn1 (f := triC), ev_push,
    ev_fn1 (f := triRootC)]

theorem snd_eq (ha : Tm env Γ a) : Thm env Γ (snd a =ₒ sub a (tri (triRoot a))) := by
  orw [fn_ev, ev_sndC' (by otype)]

theorem ev_sndC (hl : Tms env Γ l) : Thm env Γ (ev (sndC p) l =ₒ snd (ev p l)) := by
  orw [ev_sndC' hl, snd_eq]

theorem ev_fstC' (hl : Tms env Γ l) :
    Thm env Γ (ev (fstC p) l =ₒ sub (triRoot (ev p l)) (snd (ev p l))) := by
  have hs : Thm env Γ (ev (fstC.sndC p) l =ₒ snd (ev p l)) := ev_sndC hl
  orw [ev_comp2, ev_fn2 (f := PR.subC), hs, ev_push, ev_fn1 (f := triRootC)]

theorem fst_eq (ha : Tm env Γ a) : Thm env Γ (fst a =ₒ sub (triRoot a) (snd a)) := by
  orw [fn_ev, ev_fstC' (by otype)]

theorem ev_fstC (hl : Tms env Γ l) : Thm env Γ (ev (fstC p) l =ₒ fst (ev p l)) := by
  orw [ev_fstC' hl, fst_eq]

theorem triRoot_pair (ha : Tm env Γ a) (hb : Tm env Γ b) :
    Thm env Γ (triRoot (pair a b) =ₒ add a b) := by
  orw [pair_eq ha hb, triRoot_tri_add (by otype) hb (le_add_left hb ha)]

theorem snd_pair (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (snd (pair a b) =ₒ b) := by
  orw [snd_eq, triRoot_pair ha hb, pair_eq ha hb, add_sub_cancel_left]

theorem fst_pair (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (fst (pair a b) =ₒ a) := by
  orw [fst_eq, snd_pair ha hb, triRoot_pair ha hb, add_sub_cancel]

theorem le_pair_left (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (a ≤ₒ pair a b) := by
  orw [pair_eq ha hb]
  exact le_trans ha (by otype) (by otype) (le_add_right ha hb)
    (le_trans (by otype) (by otype) (by otype) (le_tri (by otype)) (le_add_right (by otype) hb))

theorem le_pair_right (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (b ≤ₒ pair a b) := by
  orw [pair_eq ha hb]; exact le_add_left hb (by otype)

/-! ### Closed -/

theorem tri_succ_c : Thm env [] (∀ₒ a, tri (S a) =ₒ add (tri a) (S a)) := by
  ointro; exact tri_succ (by otype)

theorem tri_mono_c : Thm env [] (∀ₒ a b, a ≤ₒ b →ₒ tri a ≤ₒ tri b) := by
  ointro; ointro; ointro h; exact tri_mono (by otype) (by otype) h

theorem triRoot_eq_c :
    Thm env [] (∀ₒ n s, tri s ≤ₒ n →ₒ n <ₒ tri (S s) →ₒ triRoot n =ₒ s) := by
  ointro; ointro; ointro h1; ointro h2; olift h1
  exact triRoot_eq (by otype) (by otype) h1 h2

theorem triRoot_tri_add_c : Thm env [] (∀ₒ w j, j ≤ₒ w →ₒ triRoot (add (tri w) j) =ₒ w) := by
  ointro; ointro; ointro h; exact triRoot_tri_add (by otype) (by otype) h

theorem fst_pair_c : Thm env [] (∀ₒ a b, fst (pair a b) =ₒ a) := by
  ointro; ointro; exact fst_pair (by otype) (by otype)

theorem snd_pair_c : Thm env [] (∀ₒ a b, snd (pair a b) =ₒ b) := by
  ointro; ointro; exact snd_pair (by otype) (by otype)

theorem le_pair_left_c : Thm env [] (∀ₒ a b, a ≤ₒ pair a b) := by
  ointro; ointro; exact le_pair_left (by otype) (by otype)

theorem le_pair_right_c : Thm env [] (∀ₒ a b, b ≤ₒ pair a b) := by
  ointro; ointro; exact le_pair_right (by otype) (by otype)

end

theorem tri_zero_provable : Provable natEnv (tri zero =ₒ zero) := Thm.provable (tri_zero (Γ := []))
theorem tri_succ_provable : Provable natEnv (∀ₒ a, tri (S a) =ₒ add (tri a) (S a)) := Thm.provable tri_succ_c
theorem tri_mono_provable : Provable natEnv (∀ₒ a b, a ≤ₒ b →ₒ tri a ≤ₒ tri b) := Thm.provable tri_mono_c
theorem triRoot_spec_provable :
    Provable natEnv (∀ₒ n, tri (triRoot n) ≤ₒ n ∧ₒ n <ₒ tri (S (triRoot n))) := Thm.provable triRoot_spec_c
theorem triRoot_tri_add_provable :
    Provable natEnv (∀ₒ w j, j ≤ₒ w →ₒ triRoot (add (tri w) j) =ₒ w) := Thm.provable triRoot_tri_add_c
theorem fst_pair_provable : Provable natEnv (∀ₒ a b, fst (pair a b) =ₒ a) := Thm.provable fst_pair_c
theorem snd_pair_provable : Provable natEnv (∀ₒ a b, snd (pair a b) =ₒ b) := Thm.provable snd_pair_c
theorem le_pair_left_provable : Provable natEnv (∀ₒ a b, a ≤ₒ pair a b) := Thm.provable le_pair_left_c
theorem le_pair_right_provable : Provable natEnv (∀ₒ a b, b ≤ₒ pair a b) := Thm.provable le_pair_right_c

end Incomplete.Obj
