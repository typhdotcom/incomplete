import Incomplete.Obj.GL

/-!
# Solovay's machine

A Solovay frame (`SFrame`) is a transitive irreflexive relation `R` on the worlds `0, …, N`.
For it and the checker `chkT T`, the machine `hM T K` computes, at its own code `d` and a step
`k`, the walk `h`: `h 0 = 0`, and `h (k + 1)` is the first `b` with `h k R b` such that the first
component of `k` checks as a proof of `¬S_b`, or `h k` if there is none (`nextC`). Here
`S_b := Sb (fn f) (lit d) b` says that `h` reaches `b` and never leaves it.

The machine finds the numbers of the sentences `¬S_b` about the code numbered by its input from
that input: `fillC` is the code of an expression with two holes, filled with the numbers of
`fn f` and of `lit d` (`eval_negSC`). Externally, `h` stays among the worlds (`hN_le`), and every
move goes up `R` along a provable `¬S_b` (`hN_move`). `lvM T K a` halts exactly when `h` leaves
`a` (`lvM_eval`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

/-! ### Expressions with two holes -/

/-- The holes: projection nodes, `0` for the code's function and `1` for its input. -/
def holeF : VExpr := .proj .anonymous 0 (.sort .zero)
def holeD : VExpr := .proj .anonymous 1 (.sort .zero)

/-- `e` with its projection nodes filled: index `0` by `F`, the others by `D`. -/
def fill (F D : VExpr) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => .const c ls
  | .app f a => .app (fill F D f) (fill F D a)
  | .lam A b => .lam (fill F D A) (fill F D b)
  | .forallE A b => .forallE (fill F D A) (fill F D b)
  | .proj _ i _ => if i = 0 then F else D

/-- The number of `fill F D e` from the numbers `x` of `F` and `y` of `D`. -/
def encFill (x y : Nat) : VExpr → Nat
  | .bvar i => encExpr (.bvar i)
  | .sort u => encExpr (.sort u)
  | .const c ls => encExpr (.const c ls)
  | .app f a => 7 * PR.pair (encFill x y f) (encFill x y a) + 3
  | .lam A b => 7 * PR.pair (encFill x y A) (encFill x y b) + 4
  | .forallE A b => 7 * PR.pair (encFill x y A) (encFill x y b) + 5
  | .proj _ i _ => if i = 0 then x else y

theorem encFill_eq (F D : VExpr) : ∀ e, encFill (encExpr F) (encExpr D) e = encExpr (fill F D e)
  | .bvar _ | .sort _ | .const _ _ => rfl
  | .app f a => by simp only [encFill, fill, encExpr, encFill_eq F D f, encFill_eq F D a]
  | .lam A b => by simp only [encFill, fill, encExpr, encFill_eq F D A, encFill_eq F D b]
  | .forallE A b => by simp only [encFill, fill, encExpr, encFill_eq F D A, encFill_eq F D b]
  | .proj _ i _ => by simp only [encFill, fill]; split <;> rfl

/-- The code of `encFill`, from codes `cx` and `cy` of the numbers of the holes. -/
def fillC (cx cy : PR) : VExpr → PR
  | .bvar i => numC (encExpr (.bvar i))
  | .sort u => numC (encExpr (.sort u))
  | .const c ls => numC (encExpr (.const c ls))
  | .app f a => tagC 7 3 (cpair (fillC cx cy f) (fillC cx cy a))
  | .lam A b => tagC 7 4 (cpair (fillC cx cy A) (fillC cx cy b))
  | .forallE A b => tagC 7 5 (cpair (fillC cx cy A) (fillC cx cy b))
  | .proj _ i _ => if i = 0 then cx else cy

theorem eval_fillC (cx cy : PR) (ρ : Val) :
    ∀ e, (fillC cx cy e).eval ρ = encFill (cx.eval ρ) (cy.eval ρ) e
  | .bvar _ | .sort _ | .const _ _ => eval_numC _ _
  | .app f a => by
    simp only [fillC, encFill, eval_tagC, eval_cpair, eval_fillC cx cy ρ f, eval_fillC cx cy ρ a]
  | .lam A b => by
    simp only [fillC, encFill, eval_tagC, eval_cpair, eval_fillC cx cy ρ A, eval_fillC cx cy ρ b]
  | .forallE A b => by
    simp only [fillC, encFill, eval_tagC, eval_cpair, eval_fillC cx cy ρ A, eval_fillC cx cy ρ b]
  | .proj _ i _ => by simp only [fillC, encFill]; split <;> rfl

section
variable {F D : VExpr}

theorem fill_liftN (hF : F.ClosedN) (hD : D.ClosedN) :
    ∀ (e : VExpr) (n k : Nat), fill F D (e.liftN n k) = (fill F D e).liftN n k
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ => rfl
  | .app f a, n, k => by
    simp only [VExpr.liftN, fill, fill_liftN hF hD f, fill_liftN hF hD a]
  | .lam A b, n, k => by
    simp only [VExpr.liftN, fill, fill_liftN hF hD A, fill_liftN hF hD b]
  | .forallE A b, n, k => by
    simp only [VExpr.liftN, fill, fill_liftN hF hD A, fill_liftN hF hD b]
  | .proj _ i _, n, k => by
    simp only [VExpr.liftN, fill]
    split
    · exact (hF.liftN_eq (Nat.zero_le _)).symm
    · exact (hD.liftN_eq (Nat.zero_le _)).symm

theorem fill_lit : ∀ a, fill F D (lit a) = lit a
  | 0 => rfl
  | a + 1 => by
    show VExpr.app (fill F D succ) (fill F D (lit a)) = _
    rw [fill_lit a]; rfl

end

/-! ### The sentences -/

/-- `S_a`, over the function `F` at the input `D`: `F D` reaches `a` and never leaves it. -/
def Sb (F D : VExpr) (a : Nat) : VExpr :=
  conj (ex (app2 F D (.bvar 0) =ₒ lit a))
    (all (imp (app2 F D (.bvar 0) =ₒ lit a) (app2 F D (S (.bvar 0)) =ₒ lit a)))

theorem fill_negSb {F D : VExpr} (hF : F.ClosedN) (hD : D.ClosedN) (a : Nat) :
    fill F D (neg (Sb holeF holeD a)) = neg (Sb F D a) := by
  simp only [neg, Sb, conj, ex, all, imp, EqN, app2, S, predTy, falseS, nat, succ, fill,
    fill_liftN hF hD, fill_lit, holeF, holeD, if_true, Nat.one_ne_zero, if_false]

/-- The number of `¬S_b` about the code numbered by variable `0`, at that number. -/
def negSC (b : Nat) : PR := fillC (var 0) litC (neg (Sb holeF holeD b))

theorem eval_negSC (f : PR) (b : Nat) {ρ : Val} (h : ρ 0 = f.code) :
    (negSC b).eval ρ = encExpr (neg (Sb (fn f) (lit (ρ 0)) b)) := by
  have hx : (var 0).eval ρ = encExpr (fn f) := h
  rw [negSC, eval_fillC, hx, litC_computes ρ, encFill_eq,
    fill_negSb (Obj.fn_closed f) (lit_closed _)]

/-! ### Frames -/

/-- A transitive irreflexive relation on the worlds `0, …, N`. -/
structure SFrame where
  N : Nat
  R : Nat → Nat → Bool
  trans : ∀ {a b c}, R a b = true → R b c = true → R a c = true
  irrefl : ∀ a, R a a = false
  le : ∀ {a b}, R a b = true → a ≤ N ∧ b ≤ N

namespace SFrame
variable (K : SFrame)

/-- The worlds. -/
def worlds : List Nat := List.range (K.N + 1)

/-- The worlds `a` sees. -/
def succL (a : Nat) : List Nat := K.worlds.filter (K.R a)

theorem mem_succL {a b : Nat} : b ∈ K.succL a ↔ K.R a b = true := by
  simp only [succL, worlds, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h; have := K.le h; omega

theorem not_mem_succL_self (a : Nat) : a ∉ K.succL a := by
  rw [mem_succL, K.irrefl]; exact Bool.false_ne_true

theorem mem_worlds {a : Nat} : a ∈ K.worlds ↔ a ≤ K.N := by
  simp only [worlds, List.mem_range]; omega

end SFrame

/-! ### The machine -/

section
variable (T : Tables) (K : SFrame)

/-- At `[r, y, x]`: `0` when the first component of `y` checks as a proof of `¬S_b` about the
code numbered `x`. -/
noncomputable def qC (b : Nat) : PR := comp2 (chkT T) (ren (· + 2) (negSC b)) (fstC (var 1))

/-- The first `b` of `bs` whose `qC` is `0`, else `a`. -/
noncomputable def scC : List Nat → Nat → PR
  | [], a => num a
  | b :: bs, a => ifz (qC T b) (num b) (scC bs a)

/-- At `[r, y, x]`: the next world after `r`. -/
noncomputable def nextC : PR :=
  casc (var 0) (K.worlds.map fun a => scC T (K.succL a) a) (var 0) 0

/-- **Solovay's machine**: at `[k, x]`, the world `h k` of the walk for the code numbered `x`. -/
noncomputable def hM : PR := prec .zero (nextC T K)

/-- At `[k, x]`: `0` when the walk is at `a` at `k` and leaves it at `k + 1`. -/
noncomputable def lvM (a : Nat) : PR :=
  ifz (eqz (hM T K) (num a)) (ifz (eqz (push (hM T K) (nextC T K)) (num a)) (num 1) .zero) (num 1)

/-- At `[k, x]`: `0` when the walk is at `a` at `k`. -/
noncomputable def eqM (a : Nat) : PR := eqz (hM T K) (num a)

end

/-! ### The walk, externally -/

section
variable {T : Tables} {K : SFrame}

theorem eval_qC (b : Nat) (ρ : Val) :
    (qC T b).eval ρ =
      chkNumFor T (fun _ => true) ((negSC b).eval fun i => ρ (i + 2)) (unpair1 (ρ 1)) := by
  rw [qC, eval_comp2 (fun ρ => eval_chkT ρ), eval_ren, eval_fstC, eval_var]; rfl

theorem eval_scC (ρ : Val) (a : Nat) : ∀ bs : List Nat, (scC T bs a).eval ρ = a ∨
    ∃ b ∈ bs, (scC T bs a).eval ρ = b ∧ (qC T b).eval ρ = 0
  | [] => .inl (eval_num a ρ)
  | b :: bs => by
    simp only [scC, eval_ifz, eval_num]
    split
    · exact .inr ⟨b, .head _, rfl, ‹_›⟩
    · rcases eval_scC ρ a bs with h | ⟨c, hc, h1, h2⟩
      · exact .inl h
      · exact .inr ⟨c, .tail _ hc, h1, h2⟩

theorem eval_casc_lt (c d : PR) (ρ : Val) : ∀ (bs : List PR) (j i : Nat) (hi : i < bs.length),
    c.eval ρ = j + i → (casc c bs d j).eval ρ = bs[i].eval ρ
  | b :: bs, j, 0, _, hc => by
    simp only [casc, eval_ifz_eqz, eval_num, List.getElem_cons_zero]
    rw [if_pos (by omega)]
  | b :: bs, j, i + 1, hi, hc => by
    simp only [casc, eval_ifz_eqz, eval_num, List.getElem_cons_succ]
    rw [if_neg (by omega)]
    exact eval_casc_lt c d ρ bs (j + 1) i (by simp at hi; omega) (by omega)

theorem eval_casc_ge (c d : PR) (ρ : Val) : ∀ (bs : List PR) (j : Nat),
    j + bs.length ≤ c.eval ρ → (casc c bs d j).eval ρ = d.eval ρ
  | [], _, _ => rfl
  | b :: bs, j, h => by
    simp only [List.length_cons] at h
    simp only [casc, eval_ifz_eqz, eval_num]
    rw [if_neg (by omega)]
    exact eval_casc_ge c d ρ bs (j + 1) (by omega)

/-- The next world, externally: `a` itself, or a world `a` sees whose `qC` is `0`. -/
theorem eval_nextC (ρ : Val) : (nextC T K).eval ρ = ρ 0 ∨
    ((nextC T K).eval ρ ≠ ρ 0 → K.R (ρ 0) ((nextC T K).eval ρ) = true ∧
      (qC T ((nextC T K).eval ρ)).eval ρ = 0) := by
  by_cases ha : ρ 0 ≤ K.N
  · have e := eval_casc_lt (var 0) (var 0) ρ (K.worlds.map fun a => scC T (K.succL a) a) 0 (ρ 0)
      (by simp [SFrame.worlds]; omega) (by simp [eval_var])
    simp only [List.getElem_map, SFrame.worlds, List.getElem_range] at e
    rw [nextC, SFrame.worlds, e]
    rcases eval_scC (T := T) ρ (ρ 0) (K.succL (ρ 0)) with h | ⟨b, hb, h1, h2⟩
    · exact .inl h
    · refine .inr fun _ => ?_
      rw [h1]
      exact ⟨(K.mem_succL).1 hb, h2⟩
  · left
    rw [nextC, eval_casc_ge _ _ _ _ _ (by simp [SFrame.worlds, eval_var]; omega)]
    rfl

/-- The walk of the code numbered `d`. -/
noncomputable def hN (T : Tables) (K : SFrame) (d k : Nat) : Nat := (hM T K).eval (val2 k d)

theorem hN_zero (d : Nat) : hN T K d 0 = 0 := rfl

theorem hN_succ (d k : Nat) :
    hN T K d (k + 1) = (nextC T K).eval (vcons (hN T K d k) (val2 k d)) := rfl

theorem hN_le (d : Nat) : ∀ k, hN T K d k ≤ K.N
  | 0 => Nat.zero_le _
  | k + 1 => by
    rw [hN_succ]
    rcases eval_nextC (T := T) (K := K) (vcons (hN T K d k) (val2 k d)) with h | h
    · rw [h]; exact hN_le d k
    · by_cases e : (nextC T K).eval (vcons (hN T K d k) (val2 k d)) = hN T K d k
      · rw [e]; exact hN_le d k
      · exact (K.le (h e).1).2

/-- **A move of the walk** goes up `R`, along a proof of `¬S_b` checked at the first component
of the step. -/
theorem hN_move {d k : Nat} (h : hN T K d (k + 1) ≠ hN T K d k) :
    K.R (hN T K d k) (hN T K d (k + 1)) = true ∧
      chkNumFor T (fun _ => true) ((negSC (hN T K d (k + 1))).eval (vcons d fun _ => 0))
        (unpair1 k) = 0 := by
  rw [hN_succ] at h ⊢
  rcases eval_nextC (T := T) (K := K) (vcons (hN T K d k) (val2 k d)) with e | e
  · exact absurd e h
  · obtain ⟨h1, h2⟩ := e h
    refine ⟨h1, ?_⟩
    rw [eval_qC] at h2
    exact h2

theorem lvM_eval {a d k : Nat} (h : (lvM T K a).eval (val2 k d) = 0) :
    hN T K d k = a ∧ hN T K d (k + 1) ≠ a := by
  simp only [lvM, eval_ifz_eqz, eval_num, PR.eval] at h
  rw [hN_succ]
  split at h
  · split at h
    · exact absurd h Nat.one_ne_zero
    · exact ⟨‹_›, ‹_›⟩
  · exact absurd h Nat.one_ne_zero

end

end Incomplete.Obj
