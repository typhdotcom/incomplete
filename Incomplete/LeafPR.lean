import Incomplete.CheckPR
import Incomplete.Bounded

/-!
# The fragment's certificates are decided by a code

`leafC` computes `leafNum`, which is `0` exactly when the numbered certificate keeps the
fragment's bounds (`Cert.leafOK`), by course-of-values recursion over certificate numbers. With
the proof checker it decides provability in the fragment: `bcheckDecidable`.
-/

namespace Lean4Lean.Incomplete
open PR

attribute [local simp] eval_eqz eval_succ

noncomputable def leafNum (n : Nat) : Nat := if (decCert n).leafOK then 0 else 1

theorem leafNum_eq_zero {n : Nat} : leafNum n = 0 ↔ (decCert n).leafOK = true := by
  unfold leafNum; split <;> simp_all

theorem leafNum_le (n : Nat) : leafNum n ≤ 1 := by unfold leafNum; split <;> omega

theorem eq_leafNum {n v : Nat} (h1 : v ≤ 1) (h2 : v = 0 ↔ (decCert n).leafOK = true) :
    v = leafNum n := by
  unfold leafNum; split <;> rename_i h
  · exact h2.2 h
  · have := mt h2.1 h; omega

theorem levNum_enc (l : VLevel) : levNum (encLevel l) = if l.WF 0 then l.eval [] + 1 else 0 := by
  simp [levNum, decLevel_enc]

/-! ### Levels -/

/-- `0` exactly when the level numbered by the value of `L` is closed and at most `1`. -/
def le1C (L : PR) : PR := andz (notz (levAt L)) (leq (levAt L) (num 2))

@[simp] theorem eval_le1C (L : PR) (ρ : Val) : (le1C L).eval ρ =
    if (decLevel (L.eval ρ)).WF 0 ∧ (decLevel (L.eval ρ)).eval [] ≤ 1 then 0 else 1 := by
  rw [le1C, eval_andz, eval_notz, eval_leq, eval_levAt, eval_num, ← encLevel_dec (L.eval ρ),
    levNum_enc, decLevel_enc]
  by_cases h : (decLevel (L.eval ρ)).WF 0 <;> by_cases h2 : (decLevel (L.eval ρ)).eval [] ≤ 1 <;>
    simp [h, h2] <;> omega

def le1Step : PR :=
  ifz (var 0) (num 0) (andz (le1C (fstC (leq (var 0) (num 1)))) (histAt (sndC (leq (var 0) (num 1)))))
def le1F (n h : Nat) : Nat := le1Step.eval (val2 n h)
theorem le1Step_computes : Computes2 le1Step le1F := by
  intro ρ; simp [le1F, le1Step, val2, eval_var]

theorem le1F_eq : ∀ ls : List VLevel,
    cov le1F (encList encLevel ls) = if ∀ l ∈ ls, l.WF 0 ∧ l.eval [] ≤ 1 then 0 else 1
  | [] => by rw [cov, le1F]; simp [le1Step, val2, eval_var, encList]
  | a :: ls => by
    rw [cov, le1F]
    have hlt : encList encLevel ls < encList encLevel (a :: ls) := by
      have := pair_ge_right (encLevel a) (encList encLevel ls); simp only [encList]; omega
    simp only [le1Step, val2, eval_ifz, eval_var, vcons_zero, vcons_succ, eval_num, eval_andz,
      eval_le1C, eval_histAt, eval_fstC, eval_sndC, eval_leq, encList, Nat.add_sub_cancel,
      unpair1_pair, unpair2_pair, Nat.add_one_ne_zero, if_false, decLevel_enc]
    rw [nthN_histN' _ (by simpa [encList] using hlt), le1F_eq ls]
    simp only [List.mem_cons, forall_eq_or_imp]
    by_cases h1 : a.WF 0 ∧ a.eval [] ≤ 1 <;> by_cases h2 : ∀ l ∈ ls, l.WF 0 ∧ l.eval [] ≤ 1 <;>
      simp [h1, h2]

/-- `0` exactly when every level of the list numbered by the value of `L` is closed and at
most `1`. -/
def le1At (L : PR) : PR := push L (covC le1Step)

@[simp] theorem eval_le1At (L : PR) (ρ : Val) : (le1At L).eval ρ =
    if ∀ l ∈ decList decLevel (L.eval ρ), l.WF 0 ∧ l.eval [] ≤ 1 then 0 else 1 := by
  rw [le1At, eval_push (covC_computes le1Step_computes), ← encList_dec encLevel_dec (L.eval ρ),
    le1F_eq, decList_enc decLevel_enc]

/-! ### The rules -/

/-- `a`, as `0` or `1`. -/
def nz (a : PR) : PR := andz a (num 0)

@[simp] theorem eval_nz (a : PR) (ρ : Val) : (nz a).eval ρ = if a.eval ρ = 0 then 0 else 1 := by
  simp [nz]

def leafRule : Nat → PR
  | 0 => num 0
  | 1 => histAt (restC 1 xC)
  | 2 => andz (histAt (fldC 2 xC)) (histAt (restC 3 xC))
  | 3 => nz (eqz (levAt (fldC 1 xC)) (num 1))
  | 4 => le1At (fldC 3 xC)
  | 5 | 6 => andz (histAt (fldC 7 xC)) (histAt (restC 8 xC))
  | 7 => andz (andz (le1C (fldC 1 xC)) (le1C (fldC 2 xC)))
      (andz (histAt (fldC 7 xC)) (histAt (restC 8 xC)))
  | 8 => andz (histAt (fldC 4 xC)) (histAt (restC 5 xC))
  | 9 => andz (histAt (fldC 5 xC)) (histAt (restC 6 xC))
  | 10 => histAt (restC 4 xC)
  | 11 => andz (andz (histAt (fldC 4 xC)) (histAt (fldC 5 xC))) (histAt (restC 6 xC))
  | 12 => le1At (restC 2 xC)
  | _ => num 1

/-- The history in variable `1` holds `leafNum` below the number in variable `0`. -/
def HistL (ρ : Val) : Prop := ∀ c, c < ρ 0 → nthN (ρ 1) (ρ 0 - 1 - c) = leafNum c

theorem leafRule_spec {t : Nat} {ρ : Val} (h : ρ 0 % 16 = t) (hv : HistL ρ) :
    (leafRule t).eval ρ = leafNum (ρ 0) := by
  by_cases h0 : t = 0
  · subst h0
    simp [leafRule, leafNum, decCert_bvar h, Cert.leafOK]
  have hf : ∀ i, (histAt (fldC i xC)).eval ρ = leafNum (fld i (ρ 0 / 16)) := fun i => by
    rw [eval_histAt, eval_fldC, eval_xC, hv _ (fld_lt (by omega) i)]
  have hr : ∀ i, (histAt (restC i xC)).eval ρ = leafNum (rest i (ρ 0 / 16)) := fun i => by
    rw [eval_histAt, eval_restC, eval_xC, hv _ (rest_lt (by omega) i)]
  have ht : t < 16 := h ▸ Nat.mod_lt _ (by decide)
  match t, ht with
  | 1, _ => rw [leafRule, hr, leafNum, leafNum, decCert_symm h]; rfl
  | 2, _ =>
    simp only [leafRule, eval_andz, hf, hr]
    simp [leafNum, decCert_trans h, Cert.leafOK]
  | 3, _ =>
    simp only [leafRule, eval_nz, eval_eqz, eval_levAt, eval_fldC, eval_xC, eval_num]
    rw [← encLevel_dec (fld 1 (ρ 0 / 16)), levNum_enc]
    simp [leafNum, decCert_sortDF h, Cert.leafOK]
    split <;> simp_all
  | 4, _ =>
    simp only [leafRule, eval_le1At, eval_fldC, eval_xC]
    simp [leafNum, decCert_constDF h, Cert.leafOK]
  | 5, _ =>
    simp only [leafRule, eval_andz, hf, hr]
    simp [leafNum, decCert_appDF h, Cert.leafOK]
  | 6, _ =>
    simp only [leafRule, eval_andz, hf, hr]
    simp [leafNum, decCert_lamDF h, Cert.leafOK]
  | 7, _ =>
    simp only [leafRule, eval_andz, hf, hr, eval_le1C, eval_fldC, eval_xC]
    simp only [leafNum, decCert_forallEDF h, Cert.leafOK, Bool.and_eq_true, decide_eq_true_eq]
    by_cases a : (decCert (fld 7 (ρ 0 / 16))).leafOK <;>
    by_cases b : (decCert (rest 8 (ρ 0 / 16))).leafOK <;>
    by_cases c : (decLevel (fld 1 (ρ 0 / 16))).WF 0 ∧ (decLevel (fld 1 (ρ 0 / 16))).eval [] ≤ 1 <;>
    by_cases d : (decLevel (fld 2 (ρ 0 / 16))).WF 0 ∧ (decLevel (fld 2 (ρ 0 / 16))).eval [] ≤ 1 <;>
    simp_all
  | 8, _ =>
    simp only [leafRule, eval_andz, hf, hr]
    simp [leafNum, decCert_defeqDF h, Cert.leafOK]
  | 9, _ =>
    simp only [leafRule, eval_andz, hf, hr]
    simp [leafNum, decCert_beta h, Cert.leafOK]
  | 10, _ => rw [leafRule, hr, leafNum, leafNum, decCert_eta h]; rfl
  | 11, _ =>
    simp only [leafRule, eval_andz, hf, hr]
    simp [leafNum, decCert_proofIrrel h, Cert.leafOK]
  | 12, _ =>
    simp only [leafRule, eval_le1At, eval_restC, eval_xC]
    simp [leafNum, decCert_extra h, Cert.leafOK]
  | 13, _ => simp [leafRule, leafNum, decCert_projDF h, Cert.leafOK]
  | 14, _ => simp [leafRule, leafNum, decCert_projIota h, Cert.leafOK]
  | 15, _ => simp [leafRule, leafNum, decCert_projEta h, Cert.leafOK]
  | _ + 16, ht => omega

/-! ### Course-of-values recursion -/

def dispL : Nat → Nat → PR
  | 0, _ => num 1
  | k + 1, t => ifz (eqz (modC 16 (var 0)) (num t)) (leafRule t) (dispL k (t + 1))

theorem dispL_eval {ρ : Val} (hv : HistL ρ) : ∀ k t, t ≤ ρ 0 % 16 → ρ 0 % 16 < t + k →
    (dispL k t).eval ρ = leafNum (ρ 0)
  | 0, t, h1, h2 => absurd h2 (by omega)
  | k + 1, t, h1, h2 => by
    simp only [dispL, eval_ifz, eval_eqz, eval_modC (by decide : 0 < 16), eval_var, eval_num]
    by_cases ht : ρ 0 % 16 = t
    · rw [if_pos ht]; exact leafRule_spec ht hv
    · rw [if_neg ht]; exact dispL_eval hv k (t + 1) (by omega) (by omega)

def leafStep : PR := clampC (dispL 16 0)

noncomputable def leafF (n h : Nat) : Nat := leafStep.eval (val2 n h)

theorem leafStep_computes : Computes2 leafStep leafF := by
  intro ρ
  simp only [leafF, leafStep, eval_clampC]
  congr 1; funext i
  rcases i with _ | _ | i
  · rfl
  · rfl
  · simp [Function.comp, val2, show min (i + 2) 1 = 1 by omega]

theorem leafF_eq (n : Nat) : cov leafF n = leafNum n := by
  rw [cov, leafF, leafStep, eval_clampC]
  refine dispL_eval (ρ := val2 n (histN leafF n) ∘ fun i => min i 1) (fun c hc => ?_) 16 0
    (Nat.zero_le _) (Nat.mod_lt _ (by decide))
  show nthN (histN leafF n) (n - 1 - c) = leafNum c
  rw [nthN_histN _ n c hc, leafF_eq c]
termination_by n
decreasing_by exact hc

def leafC : PR := covC leafStep

theorem leafC_computes : Computes1 leafC leafNum := by
  intro ρ; rw [leafC, covC_computes leafStep_computes, leafF_eq]

end Lean4Lean.Incomplete
