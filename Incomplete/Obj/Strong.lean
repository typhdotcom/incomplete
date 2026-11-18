import Incomplete.Obj.DivMod

/-!
# Strong induction and decreasing measures

`Thm.sind`: `(∀ n, (∀ m < n, P m) → P n) → ∀ n, P n` for an open motive `P` in any context, from
the closed schema `sind_c` over a predicate variable; `osind` applies it. The measures that the
encodings decrease along: the components of `S (pair a b)`, the payload `p` of a tagged number
`k * p + t` with `t ≥ 1`, and `pair` along a smaller sum.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing

/-- `∀ m < n, P m`, for `P` over `n` in variable `0`. -/
def below (P : VExpr) : VExpr := all (imp (.bvar 0 <ₒ .bvar 1) (P.liftN 1 1))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {P : VExpr}

/-- A predicate applied. -/
theorem predAppTy' {f a : VExpr} (hf : env.HasType Γ f predTy) (ha : Tm env Γ a) :
    env.HasType Γ (.app f a) (.sort .zero) := .app' hf ha rfl

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine predAppTy' ?_ ?_) <;> otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {P : VExpr}

theorem Thm.lamI {A : VExpr} {u : VLevel} (hA : env.HasType Γ A (.sort u)) (h : Thm env (A :: Γ) P) :
    Thm env Γ (.forallE A P) :=
  let ⟨_, hp⟩ := h; ⟨_, .lam hA hp⟩

/-- Strong induction for a predicate variable `M`. -/
theorem sind_c : Thm env [] (.forallE predTy (imp
    (all (imp (all (imp (.bvar 0 <ₒ .bvar 1) (.app (.bvar 2) (.bvar 0)))) (.app (.bvar 1) (.bvar 0))))
    (all (.app (.bvar 1) (.bvar 0))))) := by
  refine Thm.lamI predTyTy ?_
  ointro H
  have hQ : Thm env [all (imp (all (imp (.bvar 0 <ₒ .bvar 1) (.app (.bvar 2) (.bvar 0))))
      (.app (.bvar 1) (.bvar 0))), predTy] (all (all (imp (.bvar 0 <ₒ .bvar 1) (.app (.bvar 3) (.bvar 0))))) := by
    oind
    · ointro; ointro hm; oexfalso; exact not_lt_zero (by otype) hm
    · ointro ih; ointro; ointro hm
      olift H
      have H2 := Thm.allE H (t := .bvar 1) (by otype)
      onorm at H2
      refine H2.mp ?_
      ointro; ointro hk
      olift ih; olift hm
      have ih2 := Thm.allE ih (t := .bvar 1) (by otype)
      onorm at ih2
      refine ih2.mp ?_
      exact lt_of_lt_of_le (by otype) (by otype) (by otype) hk
        (le_of_succ_le_succ (by otype) (by otype) hm)
  ointro
  olift hQ
  have h1 := Thm.allE (Thm.allE hQ (t := S (.bvar 0)) (by otype)) (t := .bvar 0) (by otype)
  onorm at h1
  exact h1.mp (lt_succ (by otype))

theorem beta_bvar0 {Δ : List VExpr} {Q : VExpr} (hQ : env.HasType (nat :: Δ) Q (.sort .zero)) :
    env.IsDefEq (nat :: Δ) (.app (.lam nat (Q.liftN 1 1)) (.bvar 0)) Q (.sort .zero) := by
  have := IsDefEq.beta (hQ.weakN (.succ .one) : env.HasType (nat :: nat :: Δ) _ _)
    (.bvar .zero : env.HasType (nat :: Δ) (.bvar 0) nat)
  rwa [inst_liftN_bvar] at this

theorem impDF {Q P' Q' : VExpr} (h1 : env.IsDefEq Γ P P' (.sort .zero))
    (h2 : env.IsDefEq Γ Q Q' (.sort .zero)) : env.IsDefEq Γ (imp P Q) (imp P' Q') (.sort .zero) :=
  IsDefEq.toProp (.forallEDF h1 (IsDefEq.weak h2))

theorem allDF {P' : VExpr} (h : env.IsDefEq (nat :: Γ) P P' (.sort .zero)) :
    env.IsDefEq Γ (all P) (all P') (.sort .zero) :=
  IsDefEq.toProp (.forallEDF natTy h)

/-- Strong induction: `(∀ n, (∀ m < n, P m) → P n) → ∀ n, P n`, for `P` over `n` in variable
`0`, in any context. -/
theorem Thm.sind (hP : env.HasType (nat :: Γ) P (.sort .zero))
    (h : Thm env (nat :: Γ) (imp (below P) P)) : Thm env Γ (all P) := by
  have hL : env.HasType Γ (.lam nat P) predTy := .lam natTy hP
  obtain ⟨_, hp⟩ := (sind_c (env := env)).weak0 (Γ := Γ)
  have h1 : Thm env Γ _ := ⟨_, .app hp hL⟩
  simp only [obj_simp] at h1
  have e1 := beta_bvar0 (liftN11Ty (A := nat) hP)
  have e2 := beta_bvar0 hP
  have hlt : env.HasType (nat :: nat :: Γ) (.bvar 0 <ₒ .bvar 1) (.sort .zero) := by otype
  exact (h1.conv (impDF (allDF (impDF (allDF (impDF hlt e1)) e2)) (allDF e2))).mp (Thm.allI h)

end

theorem sind_provable : Provable natEnv (.forallE predTy (imp
    (all (imp (all (imp (.bvar 0 <ₒ .bvar 1) (.app (.bvar 2) (.bvar 0)))) (.app (.bvar 1) (.bvar 0))))
    (all (.app (.bvar 1) (.bvar 0))))) := Thm.provable sind_c

/-- Start a strong induction on the goal `∀ n, P n`: the goal becomes `(∀ m < n, P m) → P n`. -/
macro "osind" : tactic => `(tactic| (refine Thm.sind ?_ ?_; otype; unfold below; try onorm))

/-! ### Measures -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {a b c d p t : VExpr} {k : Nat}

theorem lt_succ_of_le (ha : Tm env Γ a) (hb : Tm env Γ b) (h : Thm env Γ (a ≤ₒ b)) :
    Thm env Γ (a <ₒ S b) := succ_le_succ ha hb h

theorem lt_succ_pair_left (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (a <ₒ S (pair a b)) :=
  lt_succ_of_le ha (by otype) (le_pair_left ha hb)

theorem lt_succ_pair_right (ha : Tm env Γ a) (hb : Tm env Γ b) : Thm env Γ (b <ₒ S (pair a b)) :=
  lt_succ_of_le hb (by otype) (le_pair_right ha hb)

/-- The payload of a tagged number with a nonzero tag is below it. -/
theorem lt_tag (hk : 0 < k) (hp : Tm env Γ p) (ht : Tm env Γ t) :
    Thm env Γ (p <ₒ add (mul (lit k) p) (S t)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show Thm env Γ (p <ₒ add (mul (S (lit j)) p) (S t))
  ole (add (mul (lit j) p) t)

theorem le_tag (hp : Tm env Γ p) (ht : Tm env Γ t) (hk : 0 < k) :
    Thm env Γ (p ≤ₒ add (mul (lit k) p) t) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show Thm env Γ (p ≤ₒ add (mul (S (lit j)) p) t)
  ole (add (mul (lit j) p) t)

/-- `pair` grows with the sum of its components. -/
theorem pair_lt_pair (ha : Tm env Γ a) (hb : Tm env Γ b) (hc : Tm env Γ c) (hd : Tm env Γ d)
    (h : Thm env Γ (add a b <ₒ add c d)) : Thm env Γ (pair a b <ₒ pair c d) := by
  orw [pair_eq ha hb, pair_eq hc hd]
  have h1 := tri_mono (by otype) (by otype) h
  orw [tri_succ] at h1
  have h2 := le_add_left hb ha
  ole (add (sub (tri (add c d)) (add (tri (add a b)) (S (add a b)))) (add (sub (add a b) b) d)) [h1, h2]

end

end Incomplete.Obj
