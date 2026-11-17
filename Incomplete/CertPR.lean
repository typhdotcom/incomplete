import Incomplete.LevelPR
import Incomplete.CheckNum

/-!
# Checking certificates by course-of-values recursion

`certNum T R n` is `0` when the certificate numbered `n` uses only rules in `R` and checks. For a
rule with tag `t`, `certNum T R n` at `n % 16 = t` is a condition on numbers: equalities between
fields of `n / 16` and numbers built from them, and `certNum T R` at the children. Each rule's
condition has a code; `certStep` dispatches on the tag.
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

variable {T : Tables}

noncomputable def certNum (T : Tables) (R : Nat → Bool) (n : Nat) : Nat :=
  if (decCert n).usesOnly R && (decCert n).check T.env 0 T.deciders then 0 else 1

theorem certNum_eq_zero {R n} : certNum T R n = 0 ↔
    ((decCert n).usesOnly R && (decCert n).check T.env 0 T.deciders) = true := by
  unfold certNum; split <;> simp_all

theorem j_enc (c : Cert) : fld 0 (encCert c / 16) = encJudg c.j := by
  cases c <;> simp [encCert, tag_div, Cert.j]

theorem j_dec (y : Nat) : encJudg (decCert y).j = fld 0 (y / 16) := by
  conv => rhs; rw [← encCert_dec y]
  rw [j_enc]

theorem encJudg_inj {J J' : Judg} (h : encJudg J = encJudg J') : J = J' := by
  rw [← decJudg_enc J, h, decJudg_enc]

/-- A child's judgment is `J` exactly when its number's first field is `J`'s number. -/
theorem childJ_iff (y : Nat) (J : Judg) : (decCert y).j = J ↔ fld 0 (y / 16) = encJudg J := by
  rw [← j_dec]; exact ⟨congrArg _, encJudg_inj⟩

/-- The number of a judgment with decoded components. -/
@[simp] theorem encJudg_mk (g a b c : Nat) :
    encJudg ⟨decList decExpr g, decExpr a, decExpr b, decExpr c⟩ = pair g (pair a (pair b c)) := by
  simp [encJudg, encList_dec encExpr_dec, encExpr_dec]

theorem judg_eta (J : Judg) : J = ⟨J.Γ, J.e1, J.e2, J.A⟩ := rfl

@[simp] theorem decJudg_Γ (x : Nat) : (decJudg x).Γ = decList decExpr (fld 0 x) := rfl
@[simp] theorem decJudg_e1 (x : Nat) : (decJudg x).e1 = decExpr (fld 1 x) := rfl
@[simp] theorem decJudg_e2 (x : Nat) : (decJudg x).e2 = decExpr (fld 2 x) := rfl
@[simp] theorem decJudg_A (x : Nat) : (decJudg x).A = decExpr (rest 3 x) := rfl

/-! ### Conjunction of conditions -/

/-- `0` exactly when both are. -/
def andz (a b : PR) : PR := ifz a (ifz b (num 0) (num 1)) (num 1)

@[simp] theorem eval_andz (a b : PR) (ρ : Val) :
    (andz a b).eval ρ = if a.eval ρ = 0 ∧ b.eval ρ = 0 then 0 else 1 := by
  simp only [andz, eval_ifz, eval_num]; split <;> split <;> simp_all

/-- The number of the judgment with these component numbers. -/
def judgC (g a b c : PR) : PR := cpair g (cpair a (cpair b c))

@[simp] theorem eval_judgC (g a b c : PR) (ρ : Val) :
    (judgC g a b c).eval ρ = pair (g.eval ρ) (pair (a.eval ρ) (pair (b.eval ρ) (c.eval ρ))) := by
  simp [judgC]

/-- The payload of the certificate in variable `0`, and its `i`th field. -/
def xC : PR := divC 16 (var 0)
def jC : PR := fldC 0 xC
/-- The judgment number of the child certificate numbered `c`. -/
def childJC (c : PR) : PR := fldC 0 (divC 16 c)

@[simp] theorem eval_xC (ρ : Val) : xC.eval ρ = ρ 0 / 16 := by simp [xC, eval_var]
@[simp] theorem eval_jC (ρ : Val) : jC.eval ρ = fld 0 (ρ 0 / 16) := by simp [jC]
@[simp] theorem eval_childJC (c : PR) (ρ : Val) : (childJC c).eval ρ = fld 0 (c.eval ρ / 16) := by
  simp [childJC]

/-! ### Rule specifications -/

theorem rest_lt {n : Nat} (h : ¬n % 16 = 0) (i : Nat) : rest i (n / 16) < n :=
  Nat.lt_of_le_of_lt (rest_le _ _) (div_lt_of_mod (by decide) h)
theorem fld_lt {n : Nat} (h : ¬n % 16 = 0) (i : Nat) : fld i (n / 16) < n :=
  Nat.lt_of_le_of_lt (fld_le _ _) (div_lt_of_mod (by decide) h)

/-- What a rule's code may assume: the history in variable `1` holds `certNum T R` below the
certificate number in variable `0`. -/
def HistOK (T : Tables) (R : Nat → Bool) (ρ : Val) : Prop :=
  ∀ c, c < ρ 0 → nthN (ρ 1) (ρ 0 - 1 - c) = certNum T R c

/-! ### `symm` -/

theorem decCert_symm {n : Nat} (h : n % 16 = 1) :
    decCert n = .symm (decJudg (fld 0 (n / 16))) (decCert (rest 1 (n / 16))) := by
  rw [decCert]; simp [h]

def symmC : PR :=
  andz (eqz (childJC (restC 1 xC))
    (judgC (fldC 0 jC) (fldC 2 jC) (fldC 1 jC) (restC 3 jC))) (histAt (restC 1 xC))

theorem certNum_symm {R : Nat → Bool} (hR : R 1 = true) {n : Nat} (h : n % 16 = 1) :
    certNum T R n = if fld 0 (rest 1 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16)))
        (pair (fld 2 (fld 0 (n / 16))) (pair (fld 1 (fld 0 (n / 16))) (rest 3 (fld 0 (n / 16))))) ∧
      certNum T R (rest 1 (n / 16)) = 0 then 0 else 1 := by
  have e := childJ_iff (rest 1 (n / 16))
    ⟨(decJudg (fld 0 (n / 16))).Γ, (decJudg (fld 0 (n / 16))).e2, (decJudg (fld 0 (n / 16))).e1,
      (decJudg (fld 0 (n / 16))).A⟩
  simp only [decJudg_Γ, decJudg_e1, decJudg_e2, decJudg_A, encJudg_mk] at e
  unfold certNum
  rw [decCert_symm h]
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq, decJudg_Γ, decJudg_e1, decJudg_e2, decJudg_A, e]
  by_cases h1 : fld 0 (rest 1 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16)))
      (pair (fld 2 (fld 0 (n / 16))) (pair (fld 1 (fld 0 (n / 16))) (rest 3 (fld 0 (n / 16)))))
  · by_cases h2 : ((decCert (rest 1 (n / 16))).usesOnly R &&
      (decCert (rest 1 (n / 16))).check T.env 0 T.deciders) = true
    · simp_all
    · simp only [Bool.and_eq_true] at h2; simp_all
  · simp_all

theorem symmC_spec {R : Nat → Bool} (hR : R 1 = true) {ρ : Val} (h : ρ 0 % 16 = 1)
    (hv : HistOK T R ρ) : symmC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_symm hR h]
  simp [symmC, hv _ (rest_lt (by omega) 1)]

/-! ### Shared lemmas for the rules -/

theorem ite_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (a b : α) :
    (if p then a else b) = (if q then a else b) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

theorem childOK {R : Nat → Bool} (y : Nat) : certNum T R y = 0 ↔
    (decCert y).usesOnly R = true ∧ (decCert y).check T.env 0 T.deciders = true := by
  rw [certNum_eq_zero, Bool.and_eq_true]

theorem decJudg_eq_iff (x : Nat) (J : Judg) : decJudg x = J ↔ x = encJudg J :=
  ⟨fun h => by rw [← h, encJudg_dec], fun h => by rw [h, decJudg_enc]⟩

@[simp] theorem encExpr_sort_dec (u : Nat) : encExpr (.sort (decLevel u)) = 7 * u + 1 := by
  simp [encExpr, encLevel_dec]
@[simp] theorem encExpr_lam_dec (a b : Nat) :
    encExpr (.lam (decExpr a) (decExpr b)) = 7 * pair a b + 4 := by simp [encExpr, encExpr_dec]
@[simp] theorem encExpr_forallE_dec (a b : Nat) :
    encExpr (.forallE (decExpr a) (decExpr b)) = 7 * pair a b + 5 := by simp [encExpr, encExpr_dec]
@[simp] theorem encExpr_app_dec (a b : Nat) :
    encExpr (.app (decExpr a) (decExpr b)) = 7 * pair a b + 3 := by simp [encExpr, encExpr_dec]
@[simp] theorem encLevel_succ_dec (u : Nat) : encLevel (.succ (decLevel u)) = 4 * u + 1 := by
  simp [encLevel, encLevel_dec]
@[simp] theorem encLevel_imax_dec (u v : Nat) :
    encLevel (.imax (decLevel u) (decLevel v)) = 4 * pair u v + 3 := by
  simp [encLevel, encLevel_dec]
@[simp] theorem encList_cons_dec (a g : Nat) :
    encList encExpr (decExpr a :: decList decExpr g) = pair a g + 1 := by
  simp [encList, encExpr_dec, encList_dec encExpr_dec]

/-- The number of a judgment whose components are given by numbers or decoded. -/
@[simp] theorem encJudg_mk' (Γ : List VExpr) (a b c : VExpr) :
    encJudg ⟨Γ, a, b, c⟩ = pair (encList encExpr Γ) (pair (encExpr a) (pair (encExpr b) (encExpr c))) :=
  rfl

@[simp] theorem encList_decList (g : Nat) : encList encExpr (decList decExpr g) = g :=
  encList_dec encExpr_dec g

/-! ### `trans` -/

theorem decCert_trans {n : Nat} (h : n % 16 = 2) :
    decCert n = .trans (decJudg (fld 0 (n / 16))) (decExpr (fld 1 (n / 16)))
      (decCert (fld 2 (n / 16))) (decCert (rest 3 (n / 16))) := by
  rw [decCert]; simp [h]

def transC : PR :=
  andz (eqz (childJC (fldC 2 xC)) (judgC (fldC 0 jC) (fldC 1 jC) (fldC 1 xC) (restC 3 jC))) <|
  andz (eqz (childJC (restC 3 xC)) (judgC (fldC 0 jC) (fldC 1 xC) (fldC 2 jC) (restC 3 jC))) <|
  andz (histAt (fldC 2 xC)) (histAt (restC 3 xC))

theorem certNum_trans {R : Nat → Bool} (hR : R 2 = true) {n : Nat} (h : n % 16 = 2) :
    certNum T R n = if
      fld 0 (fld 2 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 1 (fld 0 (n / 16)))
        (pair (fld 1 (n / 16)) (rest 3 (fld 0 (n / 16))))) ∧
      fld 0 (rest 3 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 1 (n / 16))
        (pair (fld 2 (fld 0 (n / 16))) (rest 3 (fld 0 (n / 16))))) ∧
      certNum T R (fld 2 (n / 16)) = 0 ∧ certNum T R (rest 3 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_trans h]
  refine ite_iff ?_ _ _
  simp only [Cert.usesOnly, Cert.check, Cert.tag, hR, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq, childJ_iff, childOK, encJudg_mk', decJudg_Γ, decJudg_e1, decJudg_e2,
    decJudg_A, encList_decList, encExpr_dec]
  exact ⟨fun h => by simp_all, fun h => by simp_all⟩

theorem transC_spec {R : Nat → Bool} (hR : R 2 = true) {ρ : Val} (h : ρ 0 % 16 = 2)
    (hv : HistOK T R ρ) : transC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_trans hR h]
  simp [transC, hv _ (fld_lt (by omega) 2), hv _ (rest_lt (by omega) 3)]

theorem decExpr_eq_iff' {a b : Nat} : decExpr a = decExpr b ↔ a = b :=
  ⟨fun h => by rw [← encExpr_dec a, h, encExpr_dec], (· ▸ rfl)⟩

/-- `0` exactly when the value is not. -/
def notz (a : PR) : PR := ifz a (num 1) (num 0)

@[simp] theorem eval_notz (a : PR) (ρ : Val) : (notz a).eval ρ = if a.eval ρ = 0 then 1 else 0 := by
  simp [notz]

/-- The equations the rules' simplification uses. -/
macro "rule_simp" hR:term : tactic => `(tactic|
  simp only [Cert.usesOnly, Cert.check, Cert.tag, $hR:term, Bool.true_and, Bool.and_eq_true,
    decide_eq_true_eq, childJ_iff, childOK, decJudg_eq_iff, encJudg_mk', decJudg_Γ, decJudg_e1,
    decJudg_e2, decJudg_A, encList_decList, encExpr_dec, encExpr, encLevel, encLevel_dec,
    encList, decExpr_eq_iff', Nat.mul_zero, Nat.zero_add])

/-- Two conjunctions of the same hypotheses, in any order and grouping. -/
macro "conj_iff" : tactic => `(tactic| (constructor <;> intro h <;>
  (repeat' (rcases ‹_ ∧ _› with ⟨_, _⟩)) <;> (repeat' apply And.intro) <;>
  with_reducible assumption))

/-! ### `sortDF` -/

theorem decCert_sortDF {n : Nat} (h : n % 16 = 3) :
    decCert n = .sortDF (decJudg (fld 0 (n / 16))) (decLevel (fld 1 (n / 16)))
      (decLevel (rest 2 (n / 16))) := by
  rw [decCert]; simp [h]

def levAt (a : PR) : PR := push a levC

@[simp] theorem eval_levAt (a : PR) (ρ : Val) : (levAt a).eval ρ = levNum (a.eval ρ) :=
  eval_push levC_computes a ρ

def sortDFC : PR :=
  andz (eqz jC (judgC (fldC 0 jC) (tagC 7 1 (fldC 1 xC)) (tagC 7 1 (restC 2 xC))
    (tagC 7 1 (tagC 4 1 (fldC 1 xC))))) <|
  andz (notz (levAt (fldC 1 xC))) <|
  andz (notz (levAt (restC 2 xC))) (eqz (levAt (fldC 1 xC)) (levAt (restC 2 xC)))

theorem certNum_sortDF {R : Nat → Bool} (hR : R 3 = true) {n : Nat} (h : n % 16 = 3) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (7 * fld 1 (n / 16) + 1)
        (pair (7 * rest 2 (n / 16) + 1) (7 * (4 * fld 1 (n / 16) + 1) + 1))) ∧
      levNum (fld 1 (n / 16)) ≠ 0 ∧ levNum (rest 2 (n / 16)) ≠ 0 ∧
      levNum (fld 1 (n / 16)) = levNum (rest 2 (n / 16)) then 0 else 1 := by
  rw [certNum, decCert_sortDF h]
  refine ite_iff ?_ _ _
  rule_simp hR
  simp only [Tables.deciders, beq_iff_eq, levNum]
  by_cases a : (decLevel (fld 1 (n / 16))).WF 0 <;> by_cases b : (decLevel (rest 2 (n / 16))).WF 0 <;>
    simp [a, b]

theorem sortDFC_spec {R : Nat → Bool} (hR : R 3 = true) {ρ : Val} (h : ρ 0 % 16 = 3)
    (_ : HistOK T R ρ) : sortDFC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_sortDF hR h]
  simp only [sortDFC, eval_andz, eval_eqz, eval_notz, eval_levAt, eval_jC, eval_judgC, eval_fldC,
    eval_restC, eval_tagC, eval_xC]
  by_cases a : levNum (fld 1 (ρ 0 / 16)) = 0 <;> by_cases b : levNum (rest 2 (ρ 0 / 16)) = 0 <;>
    simp [a, b]

/-! ### `lamDF` -/

theorem decCert_lamDF {n : Nat} (h : n % 16 = 6) :
    decCert n = .lamDF (decJudg (fld 0 (n / 16))) (decLevel (fld 1 (n / 16)))
      (decExpr (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decExpr (fld 4 (n / 16)))
      (decExpr (fld 5 (n / 16))) (decExpr (fld 6 (n / 16))) (decCert (fld 7 (n / 16)))
      (decCert (rest 8 (n / 16))) := by
  rw [decCert]; simp [h]

def lamDFC : PR :=
  andz (eqz jC (judgC (fldC 0 jC) (tagC 7 4 (cpair (fldC 2 xC) (fldC 4 xC)))
    (tagC 7 4 (cpair (fldC 3 xC) (fldC 5 xC))) (tagC 7 5 (cpair (fldC 2 xC) (fldC 6 xC))))) <|
  andz (eqz (childJC (fldC 7 xC)) (judgC (fldC 0 jC) (fldC 2 xC) (fldC 3 xC) (tagC 7 1 (fldC 1 xC)))) <|
  andz (eqz (childJC (restC 8 xC)) (judgC (PR.succ (cpair (fldC 2 xC) (fldC 0 jC))) (fldC 4 xC)
    (fldC 5 xC) (fldC 6 xC))) <|
  andz (histAt (fldC 7 xC)) (histAt (restC 8 xC))

theorem certNum_lamDF {R : Nat → Bool} (hR : R 6 = true) {n : Nat} (h : n % 16 = 6) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (7 * pair (fld 2 (n / 16)) (fld 4 (n / 16)) + 4)
        (pair (7 * pair (fld 3 (n / 16)) (fld 5 (n / 16)) + 4) (7 * pair (fld 2 (n / 16)) (fld 6 (n / 16)) + 5))) ∧
      fld 0 (fld 7 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 2 (n / 16)) (pair (fld 3 (n / 16)) (7 * fld 1 (n / 16) + 1))) ∧
      fld 0 (rest 8 (n / 16) / 16) = pair (pair (fld 2 (n / 16)) (fld 0 (fld 0 (n / 16))) + 1) (pair (fld 4 (n / 16))
        (pair (fld 5 (n / 16)) (fld 6 (n / 16)))) ∧
      certNum T R (fld 7 (n / 16)) = 0 ∧ certNum T R (rest 8 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_lamDF h]
  refine ite_iff ?_ _ _
  rule_simp hR
  exact ⟨fun ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩ => ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩,
    fun ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩ => ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩⟩

theorem lamDFC_spec {R : Nat → Bool} (hR : R 6 = true) {ρ : Val} (h : ρ 0 % 16 = 6)
    (hv : HistOK T R ρ) : lamDFC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_lamDF hR h]
  simp [lamDFC, hv _ (fld_lt (by omega) 7), hv _ (rest_lt (by omega) 8)]

/-! ### `forallEDF` -/

theorem decCert_forallEDF {n : Nat} (h : n % 16 = 7) :
    decCert n = .forallEDF (decJudg (fld 0 (n / 16))) (decLevel (fld 1 (n / 16)))
      (decLevel (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decExpr (fld 4 (n / 16)))
      (decExpr (fld 5 (n / 16))) (decExpr (fld 6 (n / 16))) (decCert (fld 7 (n / 16)))
      (decCert (rest 8 (n / 16))) := by
  rw [decCert]; simp [h]

def forallEDFC : PR :=
  andz (eqz jC (judgC (fldC 0 jC) (tagC 7 5 (cpair (fldC 3 xC) (fldC 5 xC)))
    (tagC 7 5 (cpair (fldC 4 xC) (fldC 6 xC))) (tagC 7 1 (tagC 4 3 (cpair (fldC 1 xC) (fldC 2 xC)))))) <|
  andz (eqz (childJC (fldC 7 xC)) (judgC (fldC 0 jC) (fldC 3 xC) (fldC 4 xC) (tagC 7 1 (fldC 1 xC)))) <|
  andz (eqz (childJC (restC 8 xC)) (judgC (PR.succ (cpair (fldC 3 xC) (fldC 0 jC))) (fldC 5 xC)
    (fldC 6 xC) (tagC 7 1 (fldC 2 xC)))) <|
  andz (histAt (fldC 7 xC)) (histAt (restC 8 xC))

theorem certNum_forallEDF {R : Nat → Bool} (hR : R 7 = true) {n : Nat} (h : n % 16 = 7) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (7 * pair (fld 3 (n / 16)) (fld 5 (n / 16)) + 5)
        (pair (7 * pair (fld 4 (n / 16)) (fld 6 (n / 16)) + 5) (7 * (4 * pair (fld 1 (n / 16)) (fld 2 (n / 16)) + 3) + 1))) ∧
      fld 0 (fld 7 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 3 (n / 16)) (pair (fld 4 (n / 16)) (7 * fld 1 (n / 16) + 1))) ∧
      fld 0 (rest 8 (n / 16) / 16) = pair (pair (fld 3 (n / 16)) (fld 0 (fld 0 (n / 16))) + 1) (pair (fld 5 (n / 16))
        (pair (fld 6 (n / 16)) (7 * fld 2 (n / 16) + 1))) ∧
      certNum T R (fld 7 (n / 16)) = 0 ∧ certNum T R (rest 8 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_forallEDF h]
  refine ite_iff ?_ _ _
  rule_simp hR
  exact ⟨fun ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩ => ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩,
    fun ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩ => ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩⟩

theorem forallEDFC_spec {R : Nat → Bool} (hR : R 7 = true) {ρ : Val} (h : ρ 0 % 16 = 7)
    (hv : HistOK T R ρ) : forallEDFC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_forallEDF hR h]
  simp [forallEDFC, hv _ (fld_lt (by omega) 7), hv _ (rest_lt (by omega) 8)]

/-! ### `defeqDF` -/

theorem decCert_defeqDF {n : Nat} (h : n % 16 = 8) :
    decCert n = .defeqDF (decJudg (fld 0 (n / 16))) (decLevel (fld 1 (n / 16)))
      (decExpr (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decCert (fld 4 (n / 16)))
      (decCert (rest 5 (n / 16))) := by
  rw [decCert]; simp [h]

def defeqDFC : PR :=
  andz (eqz (restC 3 jC) (fldC 3 xC)) <|
  andz (eqz (childJC (fldC 4 xC)) (judgC (fldC 0 jC) (fldC 2 xC) (fldC 3 xC) (tagC 7 1 (fldC 1 xC)))) <|
  andz (eqz (childJC (restC 5 xC)) (judgC (fldC 0 jC) (fldC 1 jC) (fldC 2 jC) (fldC 2 xC))) <|
  andz (histAt (fldC 4 xC)) (histAt (restC 5 xC))

theorem certNum_defeqDF {R : Nat → Bool} (hR : R 8 = true) {n : Nat} (h : n % 16 = 8) :
    certNum T R n = if
      rest 3 (fld 0 (n / 16)) = fld 3 (n / 16) ∧
      fld 0 (fld 4 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 2 (n / 16)) (pair (fld 3 (n / 16)) (7 * fld 1 (n / 16) + 1))) ∧
      fld 0 (rest 5 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 1 (fld 0 (n / 16)))
        (pair (fld 2 (fld 0 (n / 16))) (fld 2 (n / 16)))) ∧
      certNum T R (fld 4 (n / 16)) = 0 ∧ certNum T R (rest 5 (n / 16)) = 0 then 0 else 1 := by
  rw [certNum, decCert_defeqDF h]
  refine ite_iff ?_ _ _
  rule_simp hR
  exact ⟨fun ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩ => ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩,
    fun ⟨e1, e2, e3, ⟨u1, k1⟩, u2, k2⟩ => ⟨⟨u1, u2⟩, ⟨⟨e1, e2, e3⟩, k1⟩, k2⟩⟩

theorem defeqDFC_spec {R : Nat → Bool} (hR : R 8 = true) {ρ : Val} (h : ρ 0 % 16 = 8)
    (hv : HistOK T R ρ) : defeqDFC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_defeqDF hR h]
  simp [defeqDFC, hv _ (fld_lt (by omega) 4), hv _ (rest_lt (by omega) 5)]

/-! ### `proofIrrel` -/

theorem decCert_proofIrrel {n : Nat} (h : n % 16 = 11) :
    decCert n = .proofIrrel (decJudg (fld 0 (n / 16))) (decExpr (fld 1 (n / 16)))
      (decExpr (fld 2 (n / 16))) (decExpr (fld 3 (n / 16))) (decCert (fld 4 (n / 16)))
      (decCert (fld 5 (n / 16))) (decCert (rest 6 (n / 16))) := by
  rw [decCert]; simp [h]

def proofIrrelC : PR :=
  andz (eqz jC (judgC (fldC 0 jC) (fldC 2 xC) (fldC 3 xC) (fldC 1 xC))) <|
  andz (eqz (childJC (fldC 4 xC)) (judgC (fldC 0 jC) (fldC 1 xC) (fldC 1 xC) (num 1))) <|
  andz (eqz (childJC (fldC 5 xC)) (judgC (fldC 0 jC) (fldC 2 xC) (fldC 2 xC) (fldC 1 xC))) <|
  andz (eqz (childJC (restC 6 xC)) (judgC (fldC 0 jC) (fldC 3 xC) (fldC 3 xC) (fldC 1 xC))) <|
  andz (histAt (fldC 4 xC)) (andz (histAt (fldC 5 xC)) (histAt (restC 6 xC)))

theorem certNum_proofIrrel {R : Nat → Bool} (hR : R 11 = true) {n : Nat} (h : n % 16 = 11) :
    certNum T R n = if
      fld 0 (n / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 2 (n / 16)) (pair (fld 3 (n / 16)) (fld 1 (n / 16)))) ∧
      fld 0 (fld 4 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 1 (n / 16)) (pair (fld 1 (n / 16)) 1)) ∧
      fld 0 (fld 5 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 2 (n / 16)) (pair (fld 2 (n / 16)) (fld 1 (n / 16)))) ∧
      fld 0 (rest 6 (n / 16) / 16) = pair (fld 0 (fld 0 (n / 16))) (pair (fld 3 (n / 16)) (pair (fld 3 (n / 16)) (fld 1 (n / 16)))) ∧
      certNum T R (fld 4 (n / 16)) = 0 ∧ certNum T R (fld 5 (n / 16)) = 0 ∧ certNum T R (rest 6 (n / 16)) = 0
      then 0 else 1 := by
  rw [certNum, decCert_proofIrrel h]
  refine ite_iff ?_ _ _
  rule_simp hR
  exact ⟨fun ⟨⟨⟨u1, u2⟩, u3⟩, ⟨⟨⟨e1, e2, e3, e4⟩, k1⟩, k2⟩, k3⟩ =>
      ⟨e1, e2, e3, e4, ⟨u1, k1⟩, ⟨u2, k2⟩, u3, k3⟩,
    fun ⟨e1, e2, e3, e4, ⟨u1, k1⟩, ⟨u2, k2⟩, u3, k3⟩ =>
      ⟨⟨⟨u1, u2⟩, u3⟩, ⟨⟨⟨e1, e2, e3, e4⟩, k1⟩, k2⟩, k3⟩⟩

theorem proofIrrelC_spec {R : Nat → Bool} (hR : R 11 = true) {ρ : Val} (h : ρ 0 % 16 = 11)
    (hv : HistOK T R ρ) : proofIrrelC.eval ρ = certNum T R (ρ 0) := by
  rw [certNum_proofIrrel hR h]
  simp [proofIrrelC, hv _ (fld_lt (by omega) 4), hv _ (fld_lt (by omega) 5),
    hv _ (rest_lt (by omega) 6)]

end Incomplete
