import Incomplete.CertPR
import Incomplete.InstPR

/-!
# The rules that lift: `eta` and `bvar`

`eta` compares with a lifted term; `bvar` looks a variable's type up in the context, lifting it
past the later entries (`lookNum`, by course-of-values recursion over the context and index).
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

variable {T : Tables}

@[simp] theorem encExpr_liftN_dec (n e k : Nat) :
    encExpr ((decExpr e).liftN n k) = liftNum n e k := rfl

/-! ### `eta` -/

theorem decCert_eta {n : Nat} (h : n % 16 = 10) :
    decCert n = .eta (decJudg (fld 0 (n / 16))) (decExpr (fld 1 (n / 16)))
      (decExpr (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decCert (rest 4 (n / 16))) := by
  rw [decCert]; simp [h]

def etaC : PR :=
  andz (eqz jC (judgC (fldC 0 jC)
    (tagC 7 4 (cpair (fldC 2 xC) (tagC 7 3 (cpair (liftP (num 1) (fldC 1 xC) (num 0)) (num 0)))))
    (fldC 1 xC) (tagC 7 5 (cpair (fldC 2 xC) (fldC 3 xC))))) <|
  andz (eqz (childJC (restC 4 xC)) (judgC (fldC 0 jC) (fldC 1 xC) (fldC 1 xC)
    (tagC 7 5 (cpair (fldC 2 xC) (fldC 3 xC))))) <|
  histAt (restC 4 xC)

theorem certNum_eta {R : Nat → Bool} (hR : R 10 = true) {n : Nat} (h : n % 16 = 10) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (7 * pair (fld 2 (n / 16))
        (7 * pair (liftNum 1 (fld 1 (n / 16)) 0) 0 + 3) + 4)
        (pair (fld 1 (n / 16)) (7 * pair (fld 2 (n / 16)) (fld 3 (n / 16)) + 5))) ∧
      fld 0 (rest 4 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 1 (n / 16))
        (pair (fld 1 (n / 16)) (7 * pair (fld 2 (n / 16)) (fld 3 (n / 16)) + 5))) ∧
      certNum T R (rest 4 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_eta h]
  refine ite_iff ?_ _ _
  rule_simp hR
  simp only [encExpr_liftN_dec, Nat.mul_zero]
  exact ⟨fun ⟨u, ⟨e1, e2⟩, k⟩ => ⟨e1, e2, u, k⟩, fun ⟨e1, e2, u, k⟩ => ⟨u, ⟨e1, e2⟩, k⟩⟩

theorem etaC_spec {R : Nat → Bool} (hR : R 10 = true) {ρ : Val} (h : ρ 0 % 16 = 10)
    (hv : HistOK T R ρ) : etaC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_eta hR h]
  simp [etaC, hv _ (rest_lt (by omega) 4)]

/-! ### Context lookup -/

/-- `0` when `lookupTy` fails, the number of its result plus one otherwise. -/
def lookNum (g i : Nat) : Nat :=
  match lookupTy (decList decExpr g) i with
  | none => 0
  | some A => encExpr A + 1

def lookStep : PR :=
  let G := fstC (var 0)
  let I := sndC (var 0)
  let V := histAt (cpair (sndC (leq G (num 1))) (leq I (num 1)))
  ifz G (num 0) <|
  ifz I (PR.succ (liftP (num 1) (fstC (leq G (num 1))) (num 0))) <|
  ifz V (num 0) (PR.succ (liftP (num 1) (leq V (num 1)) (num 0)))

def lookF (n h : Nat) : Nat := lookStep.eval (val2 n h)

theorem lookStep_computes : Computes2 lookStep lookF := by
  intro ρ; simp [lookF, lookStep, val2, eval_var]

theorem lookF_eq : ∀ (Γ : List VExpr) (i : Nat),
    cov lookF (pair (encList encExpr Γ) i) = lookNum (encList encExpr Γ) i
  | [], i => by
    rw [cov, lookF]; simp [lookStep, val2, eval_var, encList, lookNum, decList, lookupTy]
  | A :: Γ, 0 => by
    rw [cov, lookF]
    simp [lookStep, val2, eval_var, encList, lookNum, decList, lookupTy, decList_enc decExpr_enc,
      decExpr_enc, liftNum]
  | A :: Γ, i + 1 => by
    have hlt : pair (encList encExpr Γ) i < pair (encList encExpr (A :: Γ)) (i + 1) := by
      apply pair_lt_pair; simp only [encList]
      have := pair_ge_right (encExpr A) (encList encExpr Γ); omega
    have ih := lookF_eq Γ i
    rw [cov, lookF]
    simp only [lookStep, val2, eval_var, vcons_zero, vcons_succ, eval_ifz, eval_fstC, eval_sndC,
      eval_leq, eval_num, eval_cpair, eval_histAt, eval_succ, eval_liftP, unpair1_pair,
      unpair2_pair, encList]
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, unpair2_pair]
    rw [nthN_histN _ _ _ (by simpa [encList] using hlt), ih]
    simp only [lookNum, decList, Nat.add_sub_cancel, unpair1_pair, unpair2_pair, lookupTy,
      decList_enc decExpr_enc]
    cases lookupTy Γ i <;> simp [decExpr_enc, liftNum]

def lookC : PR := push (cpair (var 0) (var 1)) (covC lookStep)

theorem lookC_computes : Computes2 lookC lookNum := by
  intro ρ
  rw [lookC, eval_push (covC_computes lookStep_computes)]
  simp only [eval_cpair, eval_var]
  rw [← encList_dec encExpr_dec (ρ 0), lookF_eq]

/-! ### `bvar` -/

theorem decCert_bvar {n : Nat} (h : n % 16 = 0) :
    decCert n = .bvar (decJudg (fld 0 (n / 16))) (rest 1 (n / 16)) := by
  rw [decCert]; simp [h]

def bvarC : PR :=
  andz (eqz (fldC 1 jC) (tagC 7 0 (restC 1 xC))) <|
  andz (eqz (fldC 2 jC) (tagC 7 0 (restC 1 xC))) <|
  eqz (comp2 lookC (fldC 0 jC) (restC 1 xC)) (PR.succ (restC 3 jC))

theorem lookupTy_eq_iff (g i a : Nat) :
    lookupTy (decList decExpr g) i = some (decExpr a) ↔ lookNum g i = a + 1 := by
  unfold lookNum
  cases lookupTy (decList decExpr g) i with
  | none => simp
  | some A =>
    simp only [Option.some.injEq, Nat.add_right_cancel_iff]
    exact ⟨fun h => by rw [h, encExpr_dec], fun h => by rw [← h, decExpr_enc]⟩

theorem certNum_bvar {R : Nat → Bool} (hR : R 0 = true) {n : Nat} (h : n % 16 = 0) :
    certNum T R n = if
      fld 1 (fld 0 (n / 16)) = 7 * rest 1 (n / 16) + 0 ∧
      fld 2 (fld 0 (n / 16)) = 7 * rest 1 (n / 16) + 0 ∧
      lookNum (fld 0 (fld 0 (n / 16))) (rest 1 (n / 16)) = rest 3 (fld 0 (n / 16)) + 1
      then 0 else 1 := by
  rw [certNum, decCert_bvar h]
  refine ite_iff ?_ _ _
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq, decJudg_Γ, decJudg_e1, decJudg_e2, decJudg_A, lookupTy_eq_iff]
  have e1 : ∀ a b : Nat, decExpr a = .bvar b ↔ a = 7 * b + 0 := fun a b =>
    ⟨fun h => by rw [← encExpr_dec a, h]; rfl, fun h => by rw [h, Nat.add_zero, ← decExpr_enc (.bvar b)]; rfl⟩
  simp only [e1]

theorem bvarC_spec {R : Nat → Bool} (hR : R 0 = true) {ρ : Val} (h : ρ 0 % 16 = 0)
    (_ : HistOK T R ρ) : bvarC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_bvar hR h]
  simp [bvarC, eval_comp2 lookC_computes]

@[simp] theorem encExpr_inst_dec (e a k : Nat) :
    encExpr ((decExpr e).inst (decExpr a) k) = instNum e a k := rfl

/-! ### `appDF` -/

theorem decCert_appDF {n : Nat} (h : n % 16 = 5) :
    decCert n = .appDF (decJudg (fld 0 (n / 16))) (decExpr (fld 1 (n / 16)))
      (decExpr (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decExpr (fld 4 (n / 16)))
      (decExpr (fld 5 (n / 16))) (decExpr (fld 6 (n / 16))) (decCert (fld 7 (n / 16)))
      (decCert (rest 8 (n / 16))) := by
  rw [decCert]; simp [h]

def appDFC : PR :=
  andz (eqz jC (judgC (fldC 0 jC) (tagC 7 3 (cpair (fldC 3 xC) (fldC 5 xC)))
    (tagC 7 3 (cpair (fldC 4 xC) (fldC 6 xC))) (instP (fldC 2 xC) (fldC 5 xC) (num 0)))) <|
  andz (eqz (childJC (fldC 7 xC)) (judgC (fldC 0 jC) (fldC 3 xC) (fldC 4 xC)
    (tagC 7 5 (cpair (fldC 1 xC) (fldC 2 xC))))) <|
  andz (eqz (childJC (restC 8 xC)) (judgC (fldC 0 jC) (fldC 5 xC) (fldC 6 xC) (fldC 1 xC))) <|
  andz (histAt (fldC 7 xC)) (histAt (restC 8 xC))

theorem certNum_appDF {R : Nat → Bool} (hR : R 5 = true) {n : Nat} (h : n % 16 = 5) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (7 * pair (fld 3 (n / 16)) (fld 5 (n / 16)) + 3)
        (pair (7 * pair (fld 4 (n / 16)) (fld 6 (n / 16)) + 3) (instNum (fld 2 (n / 16)) (fld 5 (n / 16)) 0))) ∧
      fld 0 (fld 7 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 3 (n / 16))
        (pair (fld 4 (n / 16)) (7 * pair (fld 1 (n / 16)) (fld 2 (n / 16)) + 5))) ∧
      fld 0 (rest 8 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 5 (n / 16))
        (pair (fld 6 (n / 16)) (fld 1 (n / 16)))) ∧
      certNum T R (fld 7 (n / 16)) = 0 ∧ certNum T R (rest 8 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_appDF h]
  refine ite_iff ?_ _ _
  rule_simp hR
  simp only [encExpr_inst_dec]
  exact ⟨fun ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩ => ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩,
    fun ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩ => ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩⟩

theorem appDFC_spec {R : Nat → Bool} (hR : R 5 = true) {ρ : Val} (h : ρ 0 % 16 = 5)
    (hv : HistOK T R ρ) : appDFC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_appDF hR h]
  simp [appDFC, hv _ (fld_lt (by omega) 7), hv _ (rest_lt (by omega) 8)]

/-! ### `beta` -/

theorem decCert_beta {n : Nat} (h : n % 16 = 9) :
    decCert n = .beta (decJudg (fld 0 (n / 16))) (decExpr (fld 1 (n / 16)))
      (decExpr (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decExpr (fld 4 (n / 16)))
      (decCert (fld 5 (n / 16))) (decCert (rest 6 (n / 16))) := by
  rw [decCert]; simp [h]

def betaC : PR :=
  andz (eqz jC (judgC (fldC 0 jC)
    (tagC 7 3 (cpair (tagC 7 4 (cpair (fldC 1 xC) (fldC 2 xC))) (fldC 4 xC)))
    (instP (fldC 2 xC) (fldC 4 xC) (num 0)) (instP (fldC 3 xC) (fldC 4 xC) (num 0)))) <|
  andz (eqz (childJC (fldC 5 xC)) (judgC (PR.succ (cpair (fldC 1 xC) (fldC 0 jC))) (fldC 2 xC)
    (fldC 2 xC) (fldC 3 xC))) <|
  andz (eqz (childJC (restC 6 xC)) (judgC (fldC 0 jC) (fldC 4 xC) (fldC 4 xC) (fldC 1 xC))) <|
  andz (histAt (fldC 5 xC)) (histAt (restC 6 xC))

theorem certNum_beta {R : Nat → Bool} (hR : R 9 = true) {n : Nat} (h : n % 16 = 9) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16)))
        (pair (7 * pair (7 * pair (fld 1 (n / 16)) (fld 2 (n / 16)) + 4) (fld 4 (n / 16)) + 3)
        (pair (instNum (fld 2 (n / 16)) (fld 4 (n / 16)) 0) (instNum (fld 3 (n / 16)) (fld 4 (n / 16)) 0))) ∧
      fld 0 (fld 5 (n / 16) / 16) = pair (pair (fld 1 (n / 16)) (fld 0 (fld 0 (n / 16))) + 1)
        (pair (fld 2 (n / 16)) (pair (fld 2 (n / 16)) (fld 3 (n / 16)))) ∧
      fld 0 (rest 6 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 4 (n / 16))
        (pair (fld 4 (n / 16)) (fld 1 (n / 16)))) ∧
      certNum T R (fld 5 (n / 16)) = 0 ∧ certNum T R (rest 6 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_beta h]
  refine ite_iff ?_ _ _
  rule_simp hR
  simp only [encExpr_inst_dec]
  exact ⟨fun ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩ => ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩,
    fun ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩ => ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩⟩

theorem betaC_spec {R : Nat → Bool} (hR : R 9 = true) {ρ : Val} (h : ρ 0 % 16 = 9)
    (hv : HistOK T R ρ) : betaC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_beta hR h]
  simp [betaC, hv _ (fld_lt (by omega) 5), hv _ (rest_lt (by omega) 6)]

end Incomplete
