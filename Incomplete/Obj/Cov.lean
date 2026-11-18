import Incomplete.Obj.Cases

/-!
# Course-of-values recursion

The list codes of `PRLib` at symbolic arguments: `iter i L` drops `i` entries of the list `L`
(`iterC`), `nth L i` is its `i`th entry (`nthC`). `hist step n` (`histC`) lists the values of
`cov step` below `n`, and `cov step n` (`covC`) is `step` at `n` and that history:
`hist step (S n) = S (pair (cov step n) (hist step n))`, and the entry `d` places back in
`hist step (S (j + d))` is `cov step j` (`nth_hist`), so `cov step` at `n` reads its values below
`n` (`nth_hist_lt`). The same for the codes `histPC`/`covPC` with a parameter. `step` stays
symbolic: it needs only to read at most its first two (three) variables.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-- `iter i L`, the code `iterC` at `[i, L]`: `L` with `i` entries dropped. -/
abbrev iter (i L : VExpr) : VExpr := app2 (fn iterC) L i

/-- The tail of the list `L`. -/
abbrev tlL (L : VExpr) : VExpr := snd (sub L (lit 1))

/-- The `i`th entry of the list `L`. -/
abbrev nth (L i : VExpr) : VExpr := fst (sub (iter i L) (lit 1))

/-- The history of `cov step` below `n`. -/
abbrev hist (step : PR) (n : VExpr) : VExpr := ev (histC step) [n]

/-- Course-of-values recursion by `step`, at `n`. -/
abbrev cov (step : PR) (n : VExpr) : VExpr := ev (covC step) [n]

/-- The history of `covP step p` below `n`. -/
abbrev histP (step : PR) (p n : VExpr) : VExpr := ev (histPC step) [n, p]

/-- Course-of-values recursion by `step` with the parameter `p`, at `n`. -/
abbrev covP (step : PR) (p n : VExpr) : VExpr := ev (covPC step) [n, p]

theorem ev_take2 {f : PR} (hf : bnd f ≤ 2) (a b : VExpr) (l : List VExpr) :
    ev f (a :: b :: l) = ev f [a, b] := ev_take 2 hf _

theorem ev_take3 {f : PR} (hf : bnd f ≤ 3) (a b c : VExpr) (l : List VExpr) :
    ev f (a :: b :: c :: l) = ev f [a, b, c] := ev_take 3 hf _

section
variable {env : VEnv} [E : ObjEnv env] {Γ l : List VExpr} {a b i j n p L : VExpr} {step : PR}

/-! ### Lists -/

theorem iter_zero (hL : Tm env Γ L) : Thm env Γ (iter zero L =ₒ L) := by
  orw [fn_ev, ev_prec_zero]

theorem iter_succ (hi : Tm env Γ i) (hL : Tm env Γ L) :
    Thm env Γ (iter (S i) L =ₒ tlL (iter i L)) := by
  orw [fn_ev, ev_prec_succ, ev_sndC, ev_leq rfl, ← fn_ev]

theorem iter_succ'_c : Thm env [] (∀ₒ i L, iter (S i) L =ₒ iter i (tlL L)) := by
  oind
  · ointro; orw [iter_succ, iter_zero, iter_zero]
  · ointro ih; ointro
    olift ih
    have ih := Thm.allE ih (t := .bvar 0) (by otype)
    onorm at ih
    orw [iter_succ (i := S (.bvar 2)), ih, ← iter_succ]

theorem iter_succ' (hi : Tm env Γ i) (hL : Tm env Γ L) :
    Thm env Γ (iter (S i) L =ₒ iter i (tlL L)) := by ospec iter_succ'_c hi hL

theorem ev_nthC {L' i' : PR} (hl : Tms env Γ l) :
    Thm env Γ (ev (nthC L' i') l =ₒ nth (ev L' l) (ev i' l)) := by
  simp only [nthC, nth]
  orw [ev_fstC, ev_leq rfl, ev_comp2, ev_fn2 (f := iterC)]

theorem sub_succ_one (ha : Tm env Γ a) : Thm env Γ (sub (S a) (lit 1) =ₒ a) := by
  show Thm env Γ (sub (S a) (S zero) =ₒ a)
  orw [succ_sub_succ, sub_zero]

theorem nth_zero (ha : Tm env Γ a) (hL : Tm env Γ L) : Thm env Γ (nth (S (pair a L)) zero =ₒ a) := by
  simp only [nth]
  orw [iter_zero, sub_succ_one, fst_pair]

theorem nth_succ (ha : Tm env Γ a) (hL : Tm env Γ L) (hi : Tm env Γ i) :
    Thm env Γ (nth (S (pair a L)) (S i) =ₒ nth L i) := by
  simp only [nth]
  orw [iter_succ', sub_succ_one, snd_pair]

/-! ### Without a parameter -/

theorem hist_zero : Thm env Γ (hist step zero =ₒ zero) := by
  orw [ev_prec_zero]

theorem hist_succ (hs : bnd step ≤ 2) (hn : Tm env Γ n) :
    Thm env Γ (hist step (S n) =ₒ S (pair (cov step n) (hist step n))) := by
  orw [ev_prec_succ, ev_cpair, ev_comp2 (g := step), ev_comp2 (g := step)]
  rw [ev_take2 hs _ _ (_ :: _), ev_take2 hs _ _ (_ :: _)]
  orefl

theorem cov_eq (hs : bnd step ≤ 2) (hn : Tm env Γ n) :
    Thm env Γ (cov step n =ₒ ev step [n, hist step n]) := by
  orw [ev_comp2 (g := step)]
  rw [ev_take2 hs _ _ (_ :: _)]
  orefl

theorem nth_hist_c (hs : bnd step ≤ 2) :
    Thm env [] (∀ₒ d j, nth (hist step (S (add j d))) d =ₒ cov step j) := by
  oind
  · ointro; orw [add_zero, hist_succ hs, nth_zero]
  · ointro ih; ointro
    olift ih
    have ih := Thm.allE ih (t := .bvar 0) (by otype)
    onorm at ih
    orw [add_succ, hist_succ hs (n := S (add (.bvar 0) (.bvar 2))), nth_succ, ih]

/-- The entry `d` places back in the history at `S (j + d)` is the value at `j`. -/
theorem nth_hist (hs : bnd step ≤ 2) (hj : Tm env Γ j) (hd : Tm env Γ a) :
    Thm env Γ (nth (hist step (S (add j a))) a =ₒ cov step j) := by ospec (nth_hist_c (env := env) hs) hd hj

theorem eq_succ_add_of_lt (hj : Tm env Γ j) (hn : Tm env Γ n) (h : Thm env Γ (j <ₒ n)) :
    Thm env Γ (n =ₒ S (add j (sub n (S j)))) := by
  oring [le_elim (STy hj) hn h]

/-- The history below `n` holds the value at `j < n`, at the index `n - 1 - j`. -/
theorem nth_hist_lt (hs : bnd step ≤ 2) (hj : Tm env Γ j) (hn : Tm env Γ n) (h : Thm env Γ (j <ₒ n)) :
    Thm env Γ (nth (hist step n) (sub (sub n (lit 1)) j) =ₒ cov step j) := by
  orw [eq_succ_add_of_lt hj hn h, sub_succ_one, add_sub_cancel_left, nth_hist hs]

/-! ### With a parameter -/

theorem histP_zero (hp : Tm env Γ p) : Thm env Γ (histP step p zero =ₒ zero) := by
  orw [ev_prec_zero]

theorem histP_succ (hs : bnd step ≤ 3) (hp : Tm env Γ p) (hn : Tm env Γ n) :
    Thm env Γ (histP step p (S n) =ₒ S (pair (covP step p n) (histP step p n))) := by
  orw [ev_prec_succ, ev_cpair, ev_comp3 (g := step), ev_comp3 (g := step)]
  rw [ev_take3 hs _ _ _ (_ :: _), ev_take3 hs _ _ _ (_ :: _)]
  orefl

theorem covP_eq (hs : bnd step ≤ 3) (hp : Tm env Γ p) (hn : Tm env Γ n) :
    Thm env Γ (covP step p n =ₒ ev step [p, n, histP step p n]) := by
  orw [ev_comp3 (g := step)]
  rw [ev_take3 hs _ _ _ (_ :: _)]
  orefl

theorem nth_histP_c (hs : bnd step ≤ 3) :
    Thm env [] (∀ₒ p d j, nth (histP step p (S (add j d))) d =ₒ covP step p j) := by
  ointro
  oind
  · ointro; orw [add_zero, histP_succ hs, nth_zero]
  · ointro ih; ointro
    olift ih
    have ih := Thm.allE ih (t := .bvar 0) (by otype)
    onorm at ih
    orw [add_succ, histP_succ hs (n := S (add (.bvar 0) (.bvar 2))), nth_succ, ih]

theorem nth_histP (hs : bnd step ≤ 3) (hp : Tm env Γ p) (hj : Tm env Γ j) (hd : Tm env Γ a) :
    Thm env Γ (nth (histP step p (S (add j a))) a =ₒ covP step p j) := by
  ospec (nth_histP_c (env := env) hs) hp hd hj

theorem nth_histP_lt (hs : bnd step ≤ 3) (hp : Tm env Γ p) (hj : Tm env Γ j) (hn : Tm env Γ n)
    (h : Thm env Γ (j <ₒ n)) :
    Thm env Γ (nth (histP step p n) (sub (sub n (lit 1)) j) =ₒ covP step p j) := by
  orw [eq_succ_add_of_lt hj hn h, sub_succ_one, add_sub_cancel_left, nth_histP hs]

end
end Incomplete.Obj
