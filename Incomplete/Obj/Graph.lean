import Incomplete.Obj.Chain

/-!
# The graph of a code at its arguments

`valF f n` is the formula `ev f [x₁, …, xₙ] = v` over the variables `v = 0` and `xᵢ = i`. A
code `τ` proves it internally for `f` at arity `n` (`Ok`) when, for all terms `xs` of length
`n`, `τ` at `xs` proves the sentence `ev f [lit xs] = lit (ev f xs)`: the template of `valF f n`
with the numerals of `ev f xs` and `xs` as holes (`okF`). By induction on the first argument,
`Ok` for a code at arity `n + 1` follows from its base case and step (`okF_ind`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- The variables `s, s + 1, …, s + n - 1`. -/
def args (s : Nat) : Nat → List VExpr
  | 0 => []
  | n + 1 => .bvar s :: args (s + 1) n

/-- `f` at the variables `1, …, n` is the variable `0`. -/
def valF (f : PR) (n : Nat) : VExpr := ev f (args 1 n) =ₒ .bvar 0

/-- The codes of the variables `s + n - 1, …, s + 1, s`. -/
def argC (s : Nat) : Nat → List PR
  | 0 => []
  | n + 1 => argC (s + 1) n ++ [var s]

theorem length_args : ∀ (s n : Nat), (args s n).length = n
  | _, 0 => rfl
  | s, n + 1 => by simp only [args, List.length_cons, length_args (s + 1) n]

theorem args_map_liftN : ∀ (s n : Nat) {k : Nat}, k ≤ s →
    (args s n).map (·.liftN 1 k) = args (s + 1) n
  | _, 0, _, _ => rfl
  | s, n + 1, k, h => by
    have ih := args_map_liftN (s + 1) n (k := k) (by omega)
    simp only [args, List.map_cons, VExpr.liftN, liftVar_le h, ih, Nat.add_comm 1 s]

theorem args_map_inst : ∀ (s n : Nat) {k : Nat} (e : VExpr), k ≤ s →
    (args (s + 1) n).map (·.inst e k) = args s n
  | _, 0, _, _, _ => rfl
  | s, n + 1, k, e, h => by
    have ih := args_map_inst (s + 1) n (k := k) e (by omega)
    simp only [args, List.map_cons, VExpr.inst, instVar, if_neg (show ¬ s + 1 < k by omega),
      if_neg (show s + 1 ≠ k by omega), Nat.add_sub_cancel, ih]

theorem args_getD : ∀ (s n i : Nat), (args s n).getD i zero = if i < n then .bvar (s + i) else zero
  | _, 0, _ => rfl
  | s, n + 1, 0 => by simp [args]
  | s, n + 1, i + 1 => by
    simp only [args, List.getD_cons_succ, args_getD (s + 1) n i]
    split <;> split
    · rw [show s + 1 + i = s + (i + 1) by omega]
    · omega
    · omega
    · rfl

theorem argC_ev : ∀ (s n : Nat) (l : List VExpr), l.length = s + n →
    ((argC s n).map (ev · l)).reverse = l.drop s
  | s, 0, l, h => by simp [argC, List.drop_eq_nil_of_le (show l.length ≤ s by omega)]
  | s, n + 1, l, h => by
    simp only [argC, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      argC_ev (s + 1) n l (by omega), ev_var]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact (List.drop_eq_getElem_cons (by omega)).symm

theorem length_argC : ∀ (s n : Nat), (argC s n).length = n
  | _, 0 => rfl
  | s, n + 1 => by
    simp only [argC, List.length_append, length_argC (s + 1) n, List.length_singleton]

@[obj_simp] theorem map_liftN_lift_succ (l : List VExpr) (n k : Nat) :
    (l.map (·.liftN 1 0)).map (·.liftN n (k + 1)) = (l.map (·.liftN n k)).map (·.liftN 1 0) := by
  simp only [List.map_map]; congr 1; funext x; exact liftN_lift_succ

@[obj_simp] theorem map_lift_inst_zero (l : List VExpr) (e : VExpr) :
    (l.map (·.liftN 1 0)).map (·.inst e 0) = l := map_liftN_inst l e 0

/-- `τ` at `xs` proves that `f` at the numerals `xs` is the numeral of its value. -/
noncomputable def okF (T : PR) (f τ : PR) (n : Nat) (xs : List VExpr) : VExpr :=
  prf T (tmplH ((ev f xs :: xs).map litT) (valF f n) 0) (ev τ xs) =ₒ zero

theorem map_ev_single_liftN (f : PR) (l : List VExpr) (n k : Nat) :
    (l.map fun v => ev f [v]).map (·.liftN n k) = (l.map (·.liftN n k)).map fun v => ev f [v] := by
  simp only [List.map_map]; congr 1; funext x; exact ev_liftN f [x] n k

theorem map_ev_single_inst (f : PR) (l : List VExpr) (e : VExpr) (k : Nat) :
    (l.map fun v => ev f [v]).map (·.inst e k) = (l.map (·.inst e k)).map fun v => ev f [v] := by
  simp only [List.map_map]; congr 1; funext x; exact ev_inst f [x] e k

theorem map_litT_liftN (l : List VExpr) (n k : Nat) :
    (l.map litT).map (·.liftN n k) = (l.map (·.liftN n k)).map litT :=
  map_ev_single_liftN litC l n k

theorem map_litT_inst (l : List VExpr) (e : VExpr) (k : Nat) :
    (l.map litT).map (·.inst e k) = (l.map (·.inst e k)).map litT :=
  map_ev_single_inst litC l e k

@[obj_simp] theorem okF_liftN {T : PR} {f τ : PR} {n m k : Nat} (xs : List VExpr) :
    (okF T f τ n xs).liftN m k = okF T f τ n (xs.map (·.liftN m k)) := by
  simp only [okF, obj_simp, map_litT_liftN, List.map_cons]

@[obj_simp] theorem okF_inst {T : PR} {f τ : PR} {n k : Nat} {e : VExpr} (xs : List VExpr) :
    (okF T f τ n xs).inst e k = okF T f τ n (xs.map (·.inst e k)) := by
  simp only [okF, obj_simp, map_litT_inst, List.map_cons]

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

theorem okFTy {T : PR} {f τ : PR} {n : Nat} {xs : List VExpr} (h : Tms env Γ xs) :
    env.HasType Γ (okF T f τ n xs) (.sort .zero) := by
  unfold okF; otype

/-- `τ` proves the graph of `f` at arity `n`, internally. -/
def Ok (env : Typing) (T : PR) (f : PR) (n : Nat) (τ : PR) : Prop :=
  ∀ {Γ : List VExpr} {xs : List VExpr}, Tms env Γ xs → xs.length = n → Thm env Γ (okF T f τ n xs)

theorem lookup_rep : ∀ (m : Nat) {i : Nat}, i < m → Lookup (List.replicate m nat ++ Γ) i nat
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, 0, _ => by
    simp only [List.replicate_succ, List.cons_append]; exact VEnv.Lookup.zero' rfl
  | m + 1, i + 1, h => by
    simp only [List.replicate_succ, List.cons_append]
    exact VEnv.Lookup.succ' (lookup_rep m (by omega)) rfl

theorem bvar_rep {m i : Nat} (h : i < m) : Tm env (List.replicate m nat ++ Γ) (.bvar i) :=
  .bvar (lookup_rep m h)

theorem argsTy : ∀ {s n m : Nat}, s + n ≤ m → Tms env (List.replicate m nat ++ Γ) (args s n)
  | _, 0, _, _ => .nil
  | s, n + 1, m, h => .cons (bvar_rep (by omega)) (argsTy (s := s + 1) (by omega))

theorem allN_intro : ∀ (m : Nat) {Γ : List VExpr} {P : VExpr},
    Thm env (List.replicate m nat ++ Γ) P → Thm env Γ (allN m P)
  | 0, _, _, h => by
    simp only [allN, List.replicate_zero, List.nil_append] at h ⊢; exact h
  | m + 1, Γ, P, h => by
    refine Thm.allI (allN_intro m (Γ := nat :: Γ) ?_)
    rwa [List.replicate_succ', List.append_assoc] at h

theorem Tms.lift_lift {xs : List VExpr} {A B : VExpr} (h : Tms env Γ xs) :
    Tms env (A :: B :: Γ) ((xs.map (·.liftN 1 0)).map (·.liftN 1 0)) := h.weak.weak

/-- **Induction on the first argument.** -/
theorem okF_ind {T : PR} {f τ : PR} {n : Nat}
    (h0 : ∀ {Γ : List VExpr} {xs : List VExpr}, Tms env Γ xs → xs.length = n →
      Thm env Γ (okF T f τ (n + 1) (zero :: xs)))
    (hS : ∀ {Γ : List VExpr} {t : VExpr} {xs : List VExpr}, Tm env Γ t → Tms env Γ xs →
      xs.length = n → Thm env Γ (okF T f τ (n + 1) (t :: xs)) →
      Thm env Γ (okF T f τ (n + 1) (S t :: xs))) :
    Ok env T f (n + 1) τ := by
  intro Γ xs hxs hlen
  cases hxs with
  | nil => simp at hlen
  | @cons t xs ht hxs =>
    have hlen : xs.length = n := by simpa using hlen
    have hall : Thm env Γ (all (okF T f τ (n + 1) (.bvar 0 :: xs.map (·.liftN 1 0)))) := by
      refine Thm.ind (okFTy (.cons (.bvar .zero) hxs.weak)) ?_ ?_
      · simp only [obj_simp]; exact h0 hxs hlen
      · simp only [obj_simp]
        refine Thm.introH (okFTy (.cons (.bvar .zero) hxs.weak)) fun k => ?_
        simp only [obj_simp] at k ⊢
        exact hS (by otype) hxs.lift_lift (by simpa using hlen) k
    have := Thm.allE hall ht
    simp only [obj_simp] at this
    exact this

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine okFTy ?_); otype))

end Incomplete.Obj
