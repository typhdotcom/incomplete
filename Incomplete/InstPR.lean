import Incomplete.LiftPR

/-!
# Instantiation on numbered expressions

`instNum e a k` is the number of `(decExpr e).inst (decExpr a) k`, by the same capped
recursion as lifting; a variable at the cutoff is replaced by the lifted term.
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

theorem instN_cap (X a : VExpr) (k : Nat) :
    X.inst a k = X.inst a (min k (encExpr X + 1)) := by
  by_cases h : k ≤ encExpr X + 1
  · rw [Nat.min_eq_left h]
  · rw [(closed_enc X).instN_eq (by omega), (closed_enc X).instN_eq (by omega)]

theorem instN_cap' {Y : VExpr} {B : Nat} (hB : encExpr Y ≤ B) (a : VExpr) (k : Nat) :
    Y.inst a (min k (B + 1)) = Y.inst a k := by
  rw [instN_cap Y a k, instN_cap Y a (min k (B + 1))]; congr 1; omega

theorem instN_cap_succ {Y : VExpr} {B : Nat} (hB : encExpr Y ≤ B) (a : VExpr) (k : Nat) :
    Y.inst a (min k (B + 1) + 1) = Y.inst a (k + 1) := by
  rw [instN_cap Y a (k + 1), instN_cap Y a (min k (B + 1) + 1)]; congr 1; omega

def instNum (e a k : Nat) : Nat := encExpr ((decExpr e).inst (decExpr a) k)

/-- One step of instantiating with the term numbered in variable `0`, at the key in variable `1`. -/
def instStep : PR :=
  let E := fstC (var 1)
  let K := sndC (var 1)
  let t := modC 7 E
  let pl := divC 7 E
  ifz t (ifz (leq (PR.succ pl) K) (tagC 7 0 pl)
    (ifz (eqz pl K) (liftP K (var 0) (num 0)) (tagC 7 0 (leq pl (num 1))))) <|
  ifz (eqz t (num 1)) E <| ifz (eqz t (num 2)) E <|
  ifz (eqz t (num 3)) (tagC 7 3 (cpair (histK (fstC pl) K) (histK (sndC pl) K))) <|
  ifz (eqz t (num 4)) (tagC 7 4 (cpair (histK (fstC pl) K) (histK (sndC pl) (PR.succ K)))) <|
  ifz (eqz t (num 5)) (tagC 7 5 (cpair (histK (fstC pl) K) (histK (sndC pl) (PR.succ K)))) <|
  tagC 7 6 (cpair (fstC pl) (cpair (fstC (sndC pl)) (histK (sndC (sndC pl)) K)))

def instF (p q h : Nat) : Nat := instStep.eval (val3 p q h)

theorem instStep_computes : Computes3 instStep instF := by
  intro ρ; simp [instF, instStep, val3, eval_var]

/-- The simplification of one instantiation step at an expression's key. -/
macro "inst_simp" : tactic => `(tactic| simp (disch := omega) only [instStep, val3, eval_var, vcons_zero, vcons_succ,
  eval_ifz, eval_eqz, eval_fstC, eval_sndC, eval_modC (by decide : 0 < 7),
  eval_divC (by decide : 0 < 7), eval_num, eval_tagC, eval_cpair, eval_histK, eval_addP, eval_leq, eval_liftP,
  eval_succ, unpair1_capKey, unpair2_capKey, unpair1_pair, unpair2_pair, encExpr, tag_mod,
  tag_div, Nat.reduceEqDiff, ite_true, ite_false])

theorem instF_eq (n : Nat) : ∀ (X : VExpr) (k : Nat),
    cov (instF n) (capKey (encExpr X) k) = encExpr (X.inst (decExpr n) k) := by
  intro X
  induction X with
  | bvar i =>
    intro k
    rw [cov, instF]
    simp [instStep, val3, eval_var, capKey, encExpr, VExpr.inst, VExpr.instVar, liftNum]
    by_cases h : i < k
    · have e : i + 1 - min k (7 * i + 1) = 0 := by omega
      simp [h, e, encExpr]
    · by_cases h' : i = k
      · subst h'
        have e1 : min i (7 * i + 1) = i := by omega
        simp [e1]
      · have : i ≠ min k (7 * i + 1) := by omega
        have e : i + 1 - min k (7 * i + 1) ≠ 0 := by omega
        simp [h, h', this, e, encExpr]
  | sort u => intro k; rw [cov, instF]; simp [instStep, val3, eval_var, capKey, encExpr, VExpr.inst]
  | const c ls =>
    intro k; rw [cov, instF]; simp [instStep, val3, eval_var, capKey, encExpr, VExpr.inst]
  | app f a ihf iha =>
    intro k
    have hf := pair_ge_left (encExpr f) (encExpr a)
    have ha := pair_ge_right (encExpr f) (encExpr a)
    rw [cov, instF]; inst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihf, iha,
      instN_cap' (B := 7 * pair (encExpr f) (encExpr a) + 3) (by omega),
      instN_cap' (B := 7 * pair (encExpr f) (encExpr a) + 3) (by omega)]
    rfl
  | lam A b ihA ihb =>
    intro k
    have hA := pair_ge_left (encExpr A) (encExpr b)
    have hb := pair_ge_right (encExpr A) (encExpr b)
    rw [cov, instF]; inst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihA, ihb,
      instN_cap' (B := 7 * pair (encExpr A) (encExpr b) + 4) (by omega),
      instN_cap_succ (B := 7 * pair (encExpr A) (encExpr b) + 4) (by omega)]
    rfl
  | forallE A b ihA ihb =>
    intro k
    have hA := pair_ge_left (encExpr A) (encExpr b)
    have hb := pair_ge_right (encExpr A) (encExpr b)
    rw [cov, instF]; inst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihA, ihb,
      instN_cap' (B := 7 * pair (encExpr A) (encExpr b) + 5) (by omega),
      instN_cap_succ (B := 7 * pair (encExpr A) (encExpr b) + 5) (by omega)]
    rfl
  | proj s i e ih =>
    intro k
    have h1 := pair_ge_right (encName s) (pair i (encExpr e))
    have h2 := pair_ge_right i (encExpr e)
    rw [cov, instF]; inst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), ih,
      instN_cap' (B := 7 * pair (encName s) (pair i (encExpr e)) + 6) (by omega)]
    rfl

def instC : PR := comp2 (covPC instStep) (keyC (var 0) (var 2)) (var 1)

theorem instC_computes : Computes3 instC instNum := by
  intro ρ
  rw [instC, eval_comp2 (covPC_computes instStep_computes), eval_keyC, eval_var, eval_var,
    eval_var]
  show cov (instF (ρ 1)) (capKey (ρ 0) (ρ 2)) = _
  rw [← encExpr_dec (ρ 0), instF_eq, instNum, decExpr_enc]

/-- The number of `(decExpr e).inst (decExpr a) k`, from codes for `e`, `a`, `k`. -/
def instP (e a k : PR) : PR := comp3 instC e a k

@[simp] theorem eval_instP (e a k : PR) (ρ : Val) :
    (instP e a k).eval ρ = instNum (e.eval ρ) (a.eval ρ) (k.eval ρ) :=
  eval_comp3 instC_computes e a k ρ

end Incomplete
