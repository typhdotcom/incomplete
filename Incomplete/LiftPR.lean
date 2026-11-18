import Incomplete.LevelPR

/-!
# Lifting on numbered expressions

`liftNum n e k` is the number of `(decExpr e).liftN n k`. The cutoff `k` grows under binders,
so the recursion runs on `pair e (min k (e + 1))`: an expression's variables are below its
number, so lifting at a larger cutoff changes nothing, and the capped key decreases.
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

theorem pair_ge_left (a b : Nat) : a ≤ pair a b := by
  unfold pair
  have : a + b ≤ tri (a + b) := by
    generalize a + b = s
    induction s with
    | zero => exact Nat.le_refl _
    | succ s ih => rw [tri_succ]; omega
  omega

theorem pair_ge_right (a b : Nat) : b ≤ pair a b := by unfold pair; omega

theorem closed_enc : ∀ X : VExpr, X.ClosedN (encExpr X + 1)
  | .bvar i => by simp only [VExpr.ClosedN, encExpr]; omega
  | .sort _ | .const .. => trivial
  | .app f a => ⟨(closed_enc f).mono (by
      have := pair_ge_left (encExpr f) (encExpr a); simp only [encExpr]; omega),
    (closed_enc a).mono (by
      have := pair_ge_right (encExpr f) (encExpr a); simp only [encExpr]; omega)⟩
  | .lam A b | .forallE A b => ⟨(closed_enc A).mono (by
      have := pair_ge_left (encExpr A) (encExpr b); simp only [encExpr]; omega),
    (closed_enc b).mono (by
      have := pair_ge_right (encExpr A) (encExpr b); simp only [encExpr]; omega)⟩
  | .proj s i e => (closed_enc e).mono (by
      have := pair_ge_right (encName s) (pair i (encExpr e))
      have := pair_ge_right i (encExpr e); simp only [encExpr]; omega)

theorem liftN_cap (X : VExpr) (n k : Nat) :
    X.liftN n k = X.liftN n (min k (encExpr X + 1)) := by
  by_cases h : k ≤ encExpr X + 1
  · rw [Nat.min_eq_left h]
  · rw [(closed_enc X).liftN_eq (by omega), (closed_enc X).liftN_eq (by omega)]

def liftNum (n e k : Nat) : Nat := encExpr ((decExpr e).liftN n k)

/-- The capped key of `e` at cutoff `k`. -/
def capKey (e k : Nat) : Nat := pair e (min k (e + 1))

def keyC (e k : PR) : PR := cpair e (minP k (PR.succ e))

@[simp] theorem eval_keyC (e k : PR) (ρ : Val) :
    (keyC e k).eval ρ = capKey (e.eval ρ) (k.eval ρ) := by simp [keyC, capKey]

/-- The history in variable `2` at the capped key, below the key in variable `1`. -/
def histK (e k : PR) : PR := nthC (var 2) (leq (leq (var 1) (num 1)) (keyC e k))

@[simp] theorem eval_histK (e k : PR) (ρ : Val) :
    (histK e k).eval ρ = nthN (ρ 2) (ρ 1 - 1 - capKey (e.eval ρ) (k.eval ρ)) := by
  simp [histK, eval_var]

/-- One step of lifting by variable `0`, at the key in variable `1`. -/
def liftStep : PR :=
  let E := fstC (var 1)
  let K := sndC (var 1)
  let t := modC 7 E
  let pl := divC 7 E
  ifz t (tagC 7 0 (ifz (leq (PR.succ pl) K) pl (addP (var 0) pl))) <|
  ifz (eqz t (num 1)) E <| ifz (eqz t (num 2)) E <|
  ifz (eqz t (num 3)) (tagC 7 3 (cpair (histK (fstC pl) K) (histK (sndC pl) K))) <|
  ifz (eqz t (num 4)) (tagC 7 4 (cpair (histK (fstC pl) K) (histK (sndC pl) (PR.succ K)))) <|
  ifz (eqz t (num 5)) (tagC 7 5 (cpair (histK (fstC pl) K) (histK (sndC pl) (PR.succ K)))) <|
  tagC 7 6 (cpair (fstC pl) (cpair (fstC (sndC pl)) (histK (sndC (sndC pl)) K)))

def liftF (p q h : Nat) : Nat := liftStep.eval (val3 p q h)

theorem liftStep_computes : Computes3 liftStep liftF := by
  intro ρ; simp [liftF, liftStep, val3, eval_var]

@[simp] theorem unpair1_capKey (e k : Nat) : unpair1 (capKey e k) = e := by simp [capKey]
@[simp] theorem unpair2_capKey (e k : Nat) : unpair2 (capKey e k) = min k (e + 1) := by simp [capKey]

theorem capKey_lt {a b K K' : Nat} (h : 2 * a + 1 < b) : capKey a K' < capKey b K := by
  unfold capKey; exact pair_lt_pair (by omega)

theorem liftN_cap' {Y : VExpr} {B : Nat} (hB : encExpr Y ≤ B) (n k : Nat) :
    Y.liftN n (min k (B + 1)) = Y.liftN n k := by
  rw [liftN_cap Y n k, liftN_cap Y n (min k (B + 1))]; congr 1; omega

theorem liftN_cap_succ {Y : VExpr} {B : Nat} (hB : encExpr Y ≤ B) (n k : Nat) :
    Y.liftN n (min k (B + 1) + 1) = Y.liftN n (k + 1) := by
  rw [liftN_cap Y n (k + 1), liftN_cap Y n (min k (B + 1) + 1)]; congr 1; omega

/-- The simplification of one lifting step at an expression's key. -/
macro "lift_simp" : tactic => `(tactic| simp (disch := omega) only [liftStep, val3, eval_var, vcons_zero, vcons_succ,
  eval_ifz, eval_eqz, eval_fstC, eval_sndC, eval_modC (by decide : 0 < 7),
  eval_divC (by decide : 0 < 7), eval_num, eval_tagC, eval_cpair, eval_histK, eval_addP, eval_leq,
  eval_succ, unpair1_capKey, unpair2_capKey, unpair1_pair, unpair2_pair, encExpr, tag_mod,
  tag_div, Nat.reduceEqDiff, ite_true, ite_false])

theorem liftF_eq (n : Nat) : ∀ (X : VExpr) (k : Nat),
    cov (liftF n) (capKey (encExpr X) k) = encExpr (X.liftN n k) := by
  intro X
  induction X with
  | bvar i =>
    intro k
    rw [cov, liftF]
    simp [liftStep, val3, eval_var, capKey, encExpr, VExpr.liftN, liftVar]
    by_cases h : i < k
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  | sort u => intro k; rw [cov, liftF]; simp [liftStep, val3, eval_var, capKey, encExpr, VExpr.liftN]
  | const c ls =>
    intro k; rw [cov, liftF]; simp [liftStep, val3, eval_var, capKey, encExpr, VExpr.liftN]
  | app f a ihf iha =>
    intro k
    have hf := pair_ge_left (encExpr f) (encExpr a)
    have ha := pair_ge_right (encExpr f) (encExpr a)
    rw [cov, liftF]; lift_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihf, iha,
      liftN_cap' (B := 7 * pair (encExpr f) (encExpr a) + 3) (by omega),
      liftN_cap' (B := 7 * pair (encExpr f) (encExpr a) + 3) (by omega)]
    rfl
  | lam A b ihA ihb =>
    intro k
    have hA := pair_ge_left (encExpr A) (encExpr b)
    have hb := pair_ge_right (encExpr A) (encExpr b)
    rw [cov, liftF]; lift_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihA, ihb,
      liftN_cap' (B := 7 * pair (encExpr A) (encExpr b) + 4) (by omega),
      liftN_cap_succ (B := 7 * pair (encExpr A) (encExpr b) + 4) (by omega)]
    rfl
  | forallE A b ihA ihb =>
    intro k
    have hA := pair_ge_left (encExpr A) (encExpr b)
    have hb := pair_ge_right (encExpr A) (encExpr b)
    rw [cov, liftF]; lift_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihA, ihb,
      liftN_cap' (B := 7 * pair (encExpr A) (encExpr b) + 5) (by omega),
      liftN_cap_succ (B := 7 * pair (encExpr A) (encExpr b) + 5) (by omega)]
    rfl
  | proj s i e ih =>
    intro k
    have h1 := pair_ge_right (encName s) (pair i (encExpr e))
    have h2 := pair_ge_right i (encExpr e)
    rw [cov, liftF]; lift_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), ih,
      liftN_cap' (B := 7 * pair (encName s) (pair i (encExpr e)) + 6) (by omega)]
    rfl

def liftC : PR := comp2 (covPC liftStep) (keyC (var 1) (var 2)) (var 0)

theorem liftC_computes : Computes3 liftC liftNum := by
  intro ρ
  rw [liftC, eval_comp2 (covPC_computes liftStep_computes), eval_keyC, eval_var, eval_var,
    eval_var]
  show cov (liftF (ρ 0)) (capKey (ρ 1) (ρ 2)) = _
  rw [← encExpr_dec (ρ 1), liftF_eq, liftNum, decExpr_enc]

/-- The number of `(decExpr e).liftN n k`, from codes for `n`, `e`, `k`. -/
def liftP (n e k : PR) : PR := comp3 liftC n e k

@[simp] theorem eval_liftP (n e k : PR) (ρ : Val) :
    (liftP n e k).eval ρ = liftNum (n.eval ρ) (e.eval ρ) (k.eval ρ) :=
  eval_comp3 liftC_computes n e k ρ

end Incomplete
