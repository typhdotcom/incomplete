import Incomplete.Rules3

/-!
# Substitution by a numbered list

`substNum e R k` is the number of `(decExpr e).subst ((listS L).liftN k)`, where `L` is the
expression list numbered `R` and `listS L` sends variable `j` to `L[j]`, or to `default` past its
end. This is how a projection's type instantiates a field's type at the parameters and the
earlier projections. The recursion is capped as for lifting.
-/

namespace Incomplete
open Lean4Lean
open PR VExpr

attribute [local simp] eval_eqz eval_succ

def listS (L : List VExpr) : Subst := fun j => L.getD j default

theorem consList_eq_listS (L : List VExpr) : Subst.dflt.consList L = listS L.reverse := by
  funext j
  rw [Subst.consList_apply, listS]
  split <;> rename_i h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]; rfl

theorem liftN_listS_apply (L : List VExpr) : ∀ k i, (listS L).liftN k i =
    if i < k then .bvar i else (L.getD (i - k) default).liftN k
  | 0, i => by simp [Subst.liftN, listS]
  | k + 1, 0 => rfl
  | k + 1, i + 1 => by
    show ((listS L).liftN k i).lift = _
    rw [liftN_listS_apply L k i]
    by_cases h : i < k
    · simp [h, VExpr.lift, VExpr.liftN, liftVar]; omega
    · rw [ite_eq_right h, ite_eq_right (by omega), Nat.add_sub_add_right, VExpr.lift, liftN_liftN]

theorem Fixes_liftN (σ : Subst) : ∀ k, (σ.liftN k).Fixes k
  | 0 => .zero
  | k + 1 => (Fixes_liftN σ k).lift

theorem Fixes_mono {σ : Subst} {k j : Nat} (h : σ.Fixes k) (hj : j ≤ k) : σ.Fixes j :=
  fun i hi => h i (by omega)

theorem subst_cap (X : VExpr) (σ : Subst) (k : Nat) :
    X.subst (σ.liftN k) = X.subst (σ.liftN (min k (encExpr X + 1))) := by
  by_cases h : k ≤ encExpr X + 1
  · rw [Nat.min_eq_left h]
  · rw [(closed_enc X).subst_eq (Fixes_mono (Fixes_liftN σ k) (by omega)),
      (closed_enc X).subst_eq (Fixes_mono (Fixes_liftN σ _) (by omega))]

theorem subst_cap' {Y : VExpr} {B : Nat} (hB : encExpr Y ≤ B) (σ : Subst) (k : Nat) :
    Y.subst (σ.liftN (min k (B + 1))) = Y.subst (σ.liftN k) := by
  rw [subst_cap Y σ k, subst_cap Y σ (min k (B + 1))]; congr 2; omega

theorem subst_cap_succ {Y : VExpr} {B : Nat} (hB : encExpr Y ≤ B) (σ : Subst) (k : Nat) :
    Y.subst (σ.liftN (min k (B + 1) + 1)) = Y.subst (σ.liftN (k + 1)) := by
  rw [subst_cap Y σ (k + 1), subst_cap Y σ (min k (B + 1) + 1)]; congr 2; omega

theorem decList_length {α β : Type} (d : Nat → α) (d' : Nat → β) :
    ∀ n, (decList d n).length = (decList d' n).length
  | 0 => by simp [decList]
  | n + 1 => by
    rw [decList, decList, List.length_cons, List.length_cons, decList_length d d' (p2 n)]
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (unpair2_le n)

theorem eval_lenAt' (L : PR) (ρ : Val) :
    (lenAt L).eval ρ = (decList decExpr (L.eval ρ)).length := by
  rw [eval_lenAt, decList_length]

theorem nthN_encList_lt {α : Type} (e : α → Nat) :
    ∀ (L : List α) (j : Nat) (h : j < L.length), nthN (encList e L) j = e L[j]
  | a :: L, 0, _ => by simp [nthN, iterTl, hdN, encList]
  | a :: L, j + 1, h => by
    rw [nthN, iterTl_succ']
    have := nthN_encList_lt e L j (by simpa using h)
    simpa [tlN, encList, nthN] using this

def substNum (e R k : Nat) : Nat :=
  encExpr ((decExpr e).subst ((listS (decList decExpr R)).liftN k))

/-- The value for variable `j` of the substitution by the list numbered `R`, as a number. -/
theorem listS_num (R j : Nat) :
    encExpr ((listS (decList decExpr R)) j) =
      if j < (decList decExpr R).length then nthN R j else 1 := by
  simp only [listS]
  split <;> rename_i h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    conv => rhs; rw [← encList_dec encExpr_dec R]
    rw [nthN_encList_lt _ _ _ h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- One step of substituting by the list numbered in variable `0`, at the key in variable `1`. -/
def substStep : PR :=
  let E := fstC (var 1)
  let K := sndC (var 1)
  let t := modC 7 E
  let pl := divC 7 E
  ifz t (ifz (leq (PR.succ pl) K) (tagC 7 0 pl)
    (liftP K (ifz (leq (PR.succ (leq pl K)) (lenAt (var 0))) (nthC (var 0) (leq pl K)) (num 1))
      (num 0))) <|
  ifz (eqz t (num 1)) E <| ifz (eqz t (num 2)) E <|
  ifz (eqz t (num 3)) (tagC 7 3 (cpair (histK (fstC pl) K) (histK (sndC pl) K))) <|
  ifz (eqz t (num 4)) (tagC 7 4 (cpair (histK (fstC pl) K) (histK (sndC pl) (PR.succ K)))) <|
  ifz (eqz t (num 5)) (tagC 7 5 (cpair (histK (fstC pl) K) (histK (sndC pl) (PR.succ K)))) <|
  tagC 7 6 (cpair (fstC pl) (cpair (fstC (sndC pl)) (histK (sndC (sndC pl)) K)))

def substF (p q h : Nat) : Nat := substStep.eval (val3 p q h)

theorem substStep_computes : Computes3 substStep substF := by
  intro ρ; simp [substF, substStep, val3, eval_var]

macro "subst_simp" : tactic => `(tactic| simp (disch := omega) only [substStep, val3, eval_var,
  vcons_zero, vcons_succ, eval_ifz, eval_eqz, eval_fstC, eval_sndC, eval_modC (by decide : 0 < 7),
  eval_divC (by decide : 0 < 7), eval_num, eval_tagC, eval_cpair, eval_histK, eval_addP, eval_leq,
  eval_liftP, eval_succ, unpair1_capKey, unpair2_capKey, unpair1_pair, unpair2_pair, encExpr, tag_mod,
  tag_div, Nat.reduceEqDiff, ite_true, ite_false])

theorem substF_eq (R : Nat) : ∀ (X : VExpr) (k : Nat),
    cov (substF R) (capKey (encExpr X) k) =
      encExpr (X.subst ((listS (decList decExpr R)).liftN k)) := by
  intro X
  induction X with
  | bvar i =>
    intro k
    rw [cov, substF]
    simp only [substStep, val3, eval_var, vcons_zero, vcons_succ, eval_ifz, eval_fstC, eval_sndC,
      eval_modC (by decide : 0 < 7), eval_divC (by decide : 0 < 7), eval_num, eval_tagC,
      eval_leq, eval_succ, eval_liftP, eval_lenAt', eval_nthC, unpair1_capKey, unpair2_capKey,
      encExpr, VExpr.subst, liftN_listS_apply]
    simp only [Nat.mul_div_cancel_left _ (show 0 < 7 by decide), Nat.mul_mod_right, ite_true]
    by_cases h : i < k
    · have e : i + 1 - min k (7 * i + 1) = 0 := by omega
      simp [h, e, encExpr]
    · have e : i + 1 - min k (7 * i + 1) ≠ 0 := by omega
      have e2 : i - min k (7 * i + 1) = i - k := by omega
      rw [ite_eq_right e, ite_eq_right h, e2, liftNum, show min k (7 * i + 1) = k by omega]
      have := listS_num R (i - k)
      simp only [listS] at this
      rw [show (if i - k + 1 - (decList decExpr R).length = 0 then nthN R (i - k) else 1) =
        (if i - k < (decList decExpr R).length then nthN R (i - k) else 1) by
          by_cases hh : i - k < (decList decExpr R).length
          · rw [ite_eq_left (by omega), ite_eq_left hh]
          · rw [ite_eq_right (by omega), ite_eq_right hh], ← this, decExpr_enc]
  | sort u => intro k; rw [cov, substF]; simp [substStep, val3, eval_var, capKey, encExpr, VExpr.subst]
  | const c ls =>
    intro k; rw [cov, substF]; simp [substStep, val3, eval_var, capKey, encExpr, VExpr.subst]
  | app f a ihf iha =>
    intro k
    have hf := pair_ge_left (encExpr f) (encExpr a)
    have ha := pair_ge_right (encExpr f) (encExpr a)
    rw [cov, substF]; subst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihf, iha,
      subst_cap' (B := 7 * pair (encExpr f) (encExpr a) + 3) (by omega),
      subst_cap' (B := 7 * pair (encExpr f) (encExpr a) + 3) (by omega)]
    rfl
  | lam A b ihA ihb =>
    intro k
    have hA := pair_ge_left (encExpr A) (encExpr b)
    have hb := pair_ge_right (encExpr A) (encExpr b)
    rw [cov, substF]; subst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihA, ihb,
      subst_cap' (B := 7 * pair (encExpr A) (encExpr b) + 4) (by omega),
      subst_cap_succ (B := 7 * pair (encExpr A) (encExpr b) + 4) (by omega)]
    rfl
  | forallE A b ihA ihb =>
    intro k
    have hA := pair_ge_left (encExpr A) (encExpr b)
    have hb := pair_ge_right (encExpr A) (encExpr b)
    rw [cov, substF]; subst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), nthN_histN _ _ _ (capKey_lt (by omega)), ihA, ihb,
      subst_cap' (B := 7 * pair (encExpr A) (encExpr b) + 5) (by omega),
      subst_cap_succ (B := 7 * pair (encExpr A) (encExpr b) + 5) (by omega)]
    rfl
  | proj s i e ih =>
    intro k
    have h1 := pair_ge_right (encName s) (pair i (encExpr e))
    have h2 := pair_ge_right i (encExpr e)
    rw [cov, substF]; subst_simp
    rw [nthN_histN _ _ _ (capKey_lt (by omega)), ih,
      subst_cap' (B := 7 * pair (encName s) (pair i (encExpr e)) + 6) (by omega)]
    rfl

def substC : PR := comp2 (covPC substStep) (keyC (var 0) (var 2)) (var 1)

theorem substC_computes : Computes3 substC substNum := by
  intro ρ
  rw [substC, eval_comp2 (covPC_computes substStep_computes), eval_keyC, eval_var, eval_var,
    eval_var]
  show cov (substF (ρ 1)) (capKey (ρ 0) (ρ 2)) = _
  rw [← encExpr_dec (ρ 0), substF_eq, substNum, decExpr_enc]

/-- The number of `(decExpr e).subst ((listS (decList decExpr R)).liftN k)`. -/
def substP (e R k : PR) : PR := comp3 substC e R k

@[simp] theorem eval_substP (e R k : PR) (ρ : Val) :
    (substP e R k).eval ρ = substNum (e.eval ρ) (R.eval ρ) (k.eval ρ) :=
  eval_comp3 substC_computes e R k ρ

end Incomplete
