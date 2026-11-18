import Incomplete.Encode

/-!
# Codes on numbered data: fields, and closed level evaluation

`levNum n` is `0` when the level numbered `n` has a parameter, and its value plus one otherwise;
`levC` computes it by course-of-values recursion.
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

def restC : Nat → PR → PR
  | 0, a => a
  | i + 1, a => restC i (sndC a)

@[simp] theorem eval_restC : ∀ (i : Nat) (a : PR) (ρ : Val), (restC i a).eval ρ = rest i (a.eval ρ)
  | 0, _, _ => rfl
  | i + 1, a, ρ => by rw [restC, eval_restC i, eval_sndC]; rfl

def fldC (i : Nat) (a : PR) : PR := fstC (restC i a)

@[simp] theorem eval_fldC (i : Nat) (a : PR) (ρ : Val) : (fldC i a).eval ρ = fld i (a.eval ρ) := by
  simp [fldC, fld]

@[simp] theorem eval_ifz_eqz (a b c d : PR) (ρ : Val) :
    (ifz (eqz a b) c d).eval ρ = if a.eval ρ = b.eval ρ then c.eval ρ else d.eval ρ := by
  rw [eval_ifz]; by_cases h : a.eval ρ = b.eval ρ
  · rw [ite_eq_left ((eval_eqz _ _ _).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h ((eval_eqz _ _ _).1 e)), ite_eq_right h]

def mulP (a b : PR) : PR := comp2 mulC a b
def addP (a b : PR) : PR := comp2 addC a b
def maxP (a b : PR) : PR := addP a (leq b a)

@[simp] theorem eval_mulP (a b : PR) (ρ : Val) : (mulP a b).eval ρ = a.eval ρ * b.eval ρ :=
  eval_comp2 mulC_computes a b ρ
@[simp] theorem eval_addP (a b : PR) (ρ : Val) : (addP a b).eval ρ = a.eval ρ + b.eval ρ :=
  eval_comp2 addC_computes a b ρ
@[simp] theorem eval_maxP (a b : PR) (ρ : Val) : (maxP a b).eval ρ = max (a.eval ρ) (b.eval ρ) := by
  simp [maxP]; omega

/-- The value of the course-of-values history `var 1` at `c`, below `var 0`. -/
def histAt (c : PR) : PR := nthC (var 1) (leq (leq (var 0) (num 1)) c)

@[simp] theorem eval_histAt (c : PR) (ρ : Val) :
    (histAt c).eval ρ = nthN (ρ 1) (ρ 0 - 1 - c.eval ρ) := by
  simp [histAt, eval_var]

/-! ### Closed levels -/

def levNum (n : Nat) : Nat := if (decLevel n).WF 0 then (decLevel n).eval [] + 1 else 0

def levStep : PR :=
  ifz (var 0) (num 1) <|
    let m := leq (var 0) (num 1)
    let t := modC 4 m
    let x := divC 4 m
    let va := histAt (fstC x)
    let vb := histAt (sndC x)
    ifz t (ifz (histAt x) (num 0) (PR.succ (histAt x))) <|
    ifz (eqz t (num 1)) (ifz (mulP va vb) (num 0) (maxP va vb)) <|
    ifz (eqz t (num 2)) (ifz (mulP va vb) (num 0) (ifz (eqz vb (num 1)) (num 1) (maxP va vb))) <|
    num 0

def levF (n h : Nat) : Nat := levStep.eval (val2 n h)

theorem levStep_computes : Computes2 levStep levF := by
  intro ρ; simp [levF, levStep, eval_var, val2]

theorem levNum_succ (m : Nat) (val : Nat → Nat) (hv : ∀ c ≤ m, val c = levNum c) :
    levNum (m + 1) =
      if m % 4 = 0 then (if val (m / 4) = 0 then 0 else val (m / 4) + 1)
      else if m % 4 = 1 then
        (if val (p1 (m / 4)) * val (p2 (m / 4)) = 0 then 0
         else max (val (p1 (m / 4))) (val (p2 (m / 4))))
      else if m % 4 = 2 then
        (if val (p1 (m / 4)) * val (p2 (m / 4)) = 0 then 0
         else if val (p2 (m / 4)) = 1 then 1 else max (val (p1 (m / 4))) (val (p2 (m / 4))))
      else 0 := by
  have h4 : m / 4 ≤ m := Nat.div_le_self _ _
  rw [hv _ h4, hv _ (Nat.le_trans (unpair1_le _) h4), hv _ (Nat.le_trans (unpair2_le _) h4)]
  simp only [levNum]
  rw [decLevel]
  split
  · simp only [VLevel.WF, VLevel.eval]; split <;> simp_all
  split
  · simp only [VLevel.WF, VLevel.eval]
    by_cases ha : (decLevel (p1 (m / 4))).WF 0 <;> by_cases hb : (decLevel (p2 (m / 4))).WF 0 <;>
      simp [ha, hb, Nat.add_max_add_right]
  split
  · simp only [VLevel.WF, VLevel.eval]
    by_cases ha : (decLevel (p1 (m / 4))).WF 0 <;> by_cases hb : (decLevel (p2 (m / 4))).WF 0 <;>
      simp [ha, hb, Lean.Nat.imax]
    split <;> simp_all
  · simp [VLevel.WF]

theorem levF_eq (n : Nat) : cov levF n = levNum n := by
  have hv : ∀ c, c < n → nthN (histN levF n) (n - 1 - c) = levNum c := fun c hc => by
    rw [nthN_histN levF n c hc, levF_eq c]
  rw [cov]
  cases n with
  | zero => simp [levF, levStep, val2, eval_var, levNum, decLevel, VLevel.WF, VLevel.eval]
  | succ m =>
    rw [levNum_succ m (fun c => nthN (histN levF (m + 1)) (m + 1 - 1 - c))
      (fun c hc => hv c (Nat.lt_succ_of_le hc))]
    simp [levF, levStep, val2, eval_var]
termination_by n

def levC : PR := covC levStep

theorem levC_computes : Computes1 levC levNum := by
  intro ρ; rw [levC, covC_computes levStep_computes, levF_eq]

end Incomplete
