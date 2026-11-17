import Incomplete.ProjRules

/-!
# The proof checker as a code

`certStep T R` dispatches on the tag of the certificate number in variable `0` to the code of
its rule; course-of-values recursion over it computes `certNum T R`, and `chkC T R` adds the check
of the conclusion: `ChkComputableFor T R` holds for all tables `T` and rule sets `R`.
-/

namespace Incomplete
open Lean4Lean
open PR

attribute [local simp] eval_eqz eval_succ

variable {T : Tables}

/-- `c` evaluated with every variable past `1` read as variable `1`. -/
def clampC (c : PR) : PR := ren (fun i => min i 1) c

theorem eval_clampC (c : PR) (ρ : Val) : (clampC c).eval ρ = c.eval (ρ ∘ fun i => min i 1) :=
  eval_ren c _ ρ

noncomputable def ruleC (T : Tables) : Nat → PR
  | 0 => bvarC
  | 10 => etaC
  | 5 => appDFC
  | 4 => constDFC T.consts
  | 12 => extraC T.rules
  | 9 => betaC
  | 1 => symmC
  | 2 => transC
  | 3 => sortDFC
  | 6 => lamDFC
  | 7 => forallEDFC
  | 8 => defeqDFC
  | 11 => proofIrrelC
  | 13 => clampC (projDFC T)
  | 14 => clampC (projIotaC T)
  | 15 => clampC (projEtaC T)
  | _ => num 1

/-- A code reads only variables `0` and `1`. -/
def Reads01 (c : PR) : Prop := ∀ ρ ρ' : Val, ρ 0 = ρ' 0 → ρ 1 = ρ' 1 → c.eval ρ = c.eval ρ'

theorem ruleC_reads (t : Nat) : Reads01 (ruleC T t) := by
  intro ρ ρ' h0 h1
  match t with
  | 0 => simp [ruleC, bvarC, h0, h1, eval_comp2 lookC_computes]
  | 10 => simp [ruleC, etaC, h0, h1]
  | 5 => simp [ruleC, appDFC, h0, h1]
  | 4 => simp only [ruleC, eval_constDFC, h0]
  | 9 => simp [ruleC, betaC, h0, h1]
  | 1 => simp [ruleC, symmC, h0, h1]
  | 2 => simp [ruleC, transC, h0, h1]
  | 3 => simp [ruleC, sortDFC, h0, h1]
  | 6 => simp [ruleC, lamDFC, h0, h1]
  | 7 => simp [ruleC, forallEDFC, h0, h1]
  | 8 => simp [ruleC, defeqDFC, h0, h1]
  | 11 => simp [ruleC, proofIrrelC, h0, h1]
  | 12 => simp only [ruleC, eval_extraC, h0]
  | 13 | 14 | 15 =>
    simp only [ruleC, eval_clampC]
    congr 1; funext i; rcases i with _ | _ | i <;> simp [h0, h1]
  | _ + 16 => simp [ruleC]

theorem ruleC_spec {R : Nat → Bool} {t : Nat} (hR : R t = true) {ρ : Val}
    (h : ρ 0 % 16 = t) (hv : HistOK T R ρ) : (ruleC T t).eval ρ = certNum T R (ρ 0) := by
  match t with
  | 0 => exact bvarC_spec hR h hv
  | 10 => exact etaC_spec hR h hv
  | 5 => exact appDFC_spec hR h hv
  | 4 => exact constDFC_spec hR h hv
  | 9 => exact betaC_spec hR h hv
  | 1 => exact symmC_spec hR h hv
  | 2 => exact transC_spec hR h hv
  | 3 => exact sortDFC_spec hR h hv
  | 6 => exact lamDFC_spec hR h hv
  | 7 => exact forallEDFC_spec hR h hv
  | 8 => exact defeqDFC_spec hR h hv
  | 11 => exact proofIrrelC_spec hR h hv
  | 12 => exact extraC_spec hR h hv
  | 13 => rw [ruleC, eval_clampC]; exact projDFC_spec hR h hv
  | 14 => rw [ruleC, eval_clampC]; exact projIotaC_spec hR h hv
  | 15 => rw [ruleC, eval_clampC]; exact projEtaC_spec hR h hv
  | _ + 16 => exact absurd h (by have := Nat.mod_lt (ρ 0) (show 16 > 0 by decide); omega)

theorem tag_enc (c : Cert) : encCert c % 16 = c.tag := by
  cases c <;> simp [encCert, Cert.tag, tag_mod]

theorem tag_dec (n : Nat) : (decCert n).tag = n % 16 := by
  conv => rhs; rw [← encCert_dec n]
  rw [tag_enc]

theorem usesOnly_tag {R : Nat → Bool} : ∀ c : Cert, c.usesOnly R = true → R c.tag = true := by
  intro c h; cases c <;> simp_all [Cert.usesOnly, Cert.tag]

theorem certNum_of_not {R : Nat → Bool} {n : Nat} (h : R (n % 16) = false) : certNum T R n = 1 := by
  unfold certNum
  have : (decCert n).usesOnly R = false := by
    cases e : (decCert n).usesOnly R
    · rfl
    · have := usesOnly_tag _ e; rw [tag_dec] at this; simp_all
  simp [this]

noncomputable def dispC (T : Tables) (R : Nat → Bool) : Nat → Nat → PR
  | 0, _ => num 1
  | k + 1, t => ifz (eqz (modC 16 (var 0)) (num t))
    (if R t then ruleC T t else num 1) (dispC T R k (t + 1))

noncomputable def certStep (T : Tables) (R : Nat → Bool) : PR := dispC T R 16 0

theorem dispC_reads (R : Nat → Bool) : ∀ k t, Reads01 (dispC T R k t)
  | 0, _ => fun _ _ _ _ => rfl
  | k + 1, t => by
    intro ρ ρ' h0 h1
    have ih := dispC_reads R k (t + 1) ρ ρ' h0 h1
    have hr : (if R t then ruleC T t else num 1).eval ρ =
        (if R t then ruleC T t else num 1).eval ρ' := by
      split
      · exact ruleC_reads t ρ ρ' h0 h1
      · rfl
    simp only [dispC, eval_ifz, eval_eqz, eval_modC (by decide : 0 < 16), eval_var, eval_num, h0,
      hr, ih]

theorem dispC_eval {R : Nat → Bool} {ρ : Val}
    (hv : HistOK T R ρ) : ∀ k t, t ≤ ρ 0 % 16 → ρ 0 % 16 < t + k →
      (dispC T R k t).eval ρ = certNum T R (ρ 0)
  | 0, t, h1, h2 => absurd h2 (by omega)
  | k + 1, t, h1, h2 => by
    simp only [dispC, eval_ifz, eval_eqz, eval_modC (by decide : 0 < 16), eval_var, eval_num]
    by_cases ht : ρ 0 % 16 = t
    · rw [if_pos ht]
      cases hR : R t
      · simp only [Bool.false_eq_true, ↓reduceIte, eval_num]
        rw [certNum_of_not (ht ▸ hR)]
      · simp only [↓reduceIte]
        exact ruleC_spec hR ht hv
    · rw [if_neg ht]; exact dispC_eval hv k (t + 1) (by omega) (by omega)

noncomputable def certF (T : Tables) (R : Nat → Bool) (n h : Nat) : Nat := (certStep T R).eval (val2 n h)

theorem certStep_computes (R : Nat → Bool) : Computes2 (certStep T R) (certF T R) := by
  intro ρ; exact dispC_reads R 16 0 ρ (val2 (ρ 0) (ρ 1)) rfl rfl

theorem certF_eq (R : Nat → Bool) (n : Nat) :
    cov (certF T R) n = certNum T R n := by
  rw [cov, certF]
  refine dispC_eval (ρ := val2 n (histN (certF T R) n)) (fun c hc => ?_) 16 0 (Nat.zero_le _)
    (Nat.mod_lt _ (by decide))
  show nthN (histN (certF T R) n) (n - 1 - c) = certNum T R c
  rw [nthN_histN _ n c hc, certF_eq R c]
termination_by n
decreasing_by exact hc

noncomputable def certC (T : Tables) (R : Nat → Bool) : PR := covC (certStep T R)

theorem certC_computes (R : Nat → Bool) :
    Computes1 (certC T R) (certNum T R) := by
  intro ρ; rw [certC, covC_computes (certStep_computes R), certF_eq R]

/-! ### The conclusion -/

theorem decExpr_eq_iff {a b : Nat} : decExpr a = decExpr b ↔ a = b :=
  ⟨fun h => by rw [← encExpr_dec a, h, encExpr_dec], (· ▸ rfl)⟩

theorem j_decJudg (k : Nat) : (decCert k).j = decJudg (fld 0 (k / 16)) := by
  rw [← j_dec, decJudg_enc]

def concC : PR := fldC 0 (divC 16 (var 1))

noncomputable def chkC (T : Tables) (R : Nat → Bool) : PR :=
  andz (push (var 1) (certC T R))
    (andz (eqz (fldC 0 concC) (num 0))
      (andz (eqz (fldC 1 concC) (fldC 2 concC)) (eqz (restC 3 concC) (var 0))))

theorem chkC_computes (R : Nat → Bool) :
    Computes2 (chkC T R) (chkNumFor T R) := by
  intro ρ
  simp only [chkC, concC, eval_andz, eval_eqz, eval_push (certC_computes R), eval_var,
    eval_fldC, eval_restC, eval_divC (by decide : 0 < 16), eval_num]
  unfold chkNumFor checkProofT
  rw [j_decJudg]
  simp only [decJudg_Γ, decJudg_e1, decJudg_e2, decJudg_A, decList_eq_nil, decExpr_eq_iff]
  rw [← Bool.and_assoc]
  by_cases h : ((decCert (ρ 1)).usesOnly R &&
      (decCert (ρ 1)).check T.env 0 T.deciders) = true
  · have : certNum T R (ρ 1) = 0 := certNum_eq_zero.2 h
    simp only [this, h, Bool.true_and, decide_eq_true_eq, true_and]
    by_cases hc : fld 0 (fld 0 (ρ 1 / 16)) = 0 ∧ fld 1 (fld 0 (ρ 1 / 16)) = fld 2 (fld 0 (ρ 1 / 16)) ∧
      rest 3 (fld 0 (ρ 1 / 16)) = ρ 0
    · simp [hc]
    · simp only [not_and] at hc
      split <;> simp_all
  · have : certNum T R (ρ 1) ≠ 0 := fun e => h (certNum_eq_zero.1 e)
    simp only [this, false_and, ↓reduceIte]
    simp_all

theorem chkComputableFor (T : Tables) (R : Nat → Bool) :
    ChkComputableFor T R := ⟨chkC T R, chkC_computes R⟩

/-- **Proofs are checked by a code**, in any environment given by tables. -/
theorem checkDecidable_of_tables {env : VEnv} {T : Tables} (hT : TablesFor env T) :
    CheckDecidable env :=
  checkDecidable_of_chk hT (chkComputableFor T _)

theorem checkDecidable : CheckDecidable natEnv := checkDecidable_of_tables natEnv_tables

end Incomplete
