import Incomplete.Obj.Checker

/-!
# The checker of the fragment

`bchkT T` accepts a certificate when `chkT T` does and it keeps the bounds of `BDefEq`
(`leafC`); externally it accepts exactly the proofs of `BProvable` for tables of the
environment (`bchkNum_sound`, `bchkNum_complete`). For the fragment `bounded X` of an
environment `X` with tables `T`, it is a checker in the sense of `IsChecker`
(`IsChecker.bounded`): the closed theorems of the fragment have certificates within the bounds,
and modus ponens and instantiation at numerals stay within them (`Obj.Leaf`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- The checker of the fragment: `chkT T` on the certificate, and the bounds of `BDefEq`. -/
noncomputable def bchkT (T : Tables) : PR := andz (chkT T) (push (var 1) leafC)

/-- What `bchkT T` computes. -/
noncomputable def bchkNum (T : Tables) (s c : Nat) : Nat :=
  if chkNumFor T (fun _ => true) s c = 0 ∧ leafNum c = 0 then 0 else 1

theorem bchkT_computes (T : Tables) : Computes2 (bchkT T) (bchkNum T) := by
  intro ρ
  simp only [bchkT, eval_andz, eval_chkT, PR.eval_push leafC_computes, eval_var, bchkNum]

theorem bnd_leafC : bnd leafC ≤ 1 := by
  have := bnd_leafStep; unfold leafC; obnd

theorem bnd_bchkT (T : Tables) : bnd (bchkT T) ≤ 2 := by
  have := bnd_chkT T; have := bnd_leafC; unfold bchkT; obnd

section
variable {X : VEnv} {T : Tables} (hT : TablesFor X T)
include hT

/-- `bchkT T` accepts only proofs of the fragment. -/
theorem bchkNum_sound {P : VExpr} {k : Nat} (h : bchkNum T (encExpr P) k = 0) : BProvable X P := by
  have hc : ∀ c : Cert, c.check T.env 0 T.deciders = c.check X 0 T.deciders :=
    Cert.check_congr (fun n => (hT.consts n).symm) (fun n => (hT.inducts n).symm) 0 _
  simp only [bchkNum] at h
  split at h
  · rename_i hh
    obtain ⟨h1, h2⟩ := hh
    simp only [chkNumFor, decExpr_enc] at h1
    split at h1
    · rename_i hh
      simp only [Cert.usesOnly_all, Bool.true_and, checkProofT, Bool.and_eq_true,
        decide_eq_true_eq, hc] at hh
      obtain ⟨hk, hΓ, he, hA⟩ := hh
      have := Cert.check_bsound (Tables.deciders_spec hT) _ hk (leafNum_eq_zero.1 h2)
      rw [hΓ, hA, ← he] at this
      exact ⟨_, this⟩
    · cases h1
  · cases h

/-- Every proof of the fragment has a certificate `bchkT T` accepts. -/
theorem bchkNum_complete {P : VExpr} (h : BProvable X P) : ∃ k, bchkNum T (encExpr P) k = 0 := by
  have hc : ∀ c : Cert, c.check T.env 0 T.deciders = c.check X 0 T.deciders :=
    Cert.check_congr (fun n => (hT.consts n).symm) (fun n => (hT.inducts n).symm) 0 _
  obtain ⟨e, h⟩ := h
  obtain ⟨c, k, b, hj⟩ := Cert.check_bcomplete (Tables.deciders_spec hT) h
  refine ⟨encCert c, ?_⟩
  simp only [bchkNum, chkNumFor, decExpr_enc, decCert_enc]
  rw [ite_eq_left]
  refine ⟨?_, leafNum_eq_zero.2 (by rw [decCert_enc]; exact b)⟩
  simp [Cert.usesOnly_all, checkProofT, hc, k, hj]

end

/-! ### Inside the theory -/

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {T : Tables} {s c : VExpr}

theorem ev_leafPush (hs : Tm env Γ s) (hc : Tm env Γ c) :
    Thm env Γ (ev (push (var 1) leafC) [s, c] =ₒ leafT c) := by
  orw [ev_push (f := push (var 1) leafC) rfl (by otype)]
  rw [ev_take 1 bnd_leafC]
  simp only [List.take_succ_cons, List.take_zero]
  orefl

/-- A certificate `bchkT T` accepts is one `chkT T` accepts within the bounds. -/
theorem bprf_iff (hs : Tm env Γ s) (hc : Tm env Γ c) :
    Thm env Γ (prf (bchkT T) s c =ₒ zero) ↔
      Thm env Γ (prfT T s c =ₒ zero) ∧ Thm env Γ (leafT c =ₒ zero) := by
  have hl : Tms env Γ [s, c] := by otype
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := andz_zero hl h
    exact ⟨h1, by orw [← ev_leafPush hs hc]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ev_andz_zero rfl hl h1 (by orw [ev_leafPush hs hc]; exact h2)

end

/-- **The fragment's checker.** For tables `T` of `X`, `bchkT T` is a checker for the fragment
`bounded X`. -/
theorem IsChecker.bounded {X : VEnv} [E : ObjEnv (bounded X)] {T : Tables} (hT : TablesFor X T) :
    IsChecker (bounded X) (bchkT T) := by
  have hK := Tables.deciders_spec hT
  -- the closed certificates of the fragment
  have hcl : ∀ {e1 A : VExpr}, BDefEq X [] e1 e1 A → ∃ c : Nat,
      (decCert c).leafOK = true ∧ ∀ {Γ : List VExpr},
        Thm (Incomplete.bounded X) Γ (certT T (fun _ => true) (numT c) =ₒ zero) ∧
        Thm (Incomplete.bounded X) Γ (jT (numT c) =ₒ
          judgT zero (numT (encExpr e1)) (numT (encExpr e1)) (numT (encExpr A))) := by
    intro e1 A h
    obtain ⟨c, k, b, hj⟩ := Cert.check_bcomplete hK h
    exact ⟨encCert c, by rw [decCert_enc]; exact b, closed_cert_of hT c k hj⟩
  refine ⟨bnd_bchkT T, ?_, ?_, ?_, ?_⟩
  · intro P h
    obtain ⟨e, he⟩ := h
    obtain ⟨c, b, hc⟩ := hcl he
    refine ⟨c, fun {Γ} => (bprf_iff (by otype) (by otype)).2 ⟨?_, leafT_numT b⟩⟩
    exact prfT_of_cert (by otype) (by otype) (by otype) (hc (Γ := Γ)).1 (hc (Γ := Γ)).2
  · intro Γ ys P Q c₁ c₂ hys hc₁ hc₂ h₁ h₂
    obtain ⟨k₁, l₁⟩ := (bprf_iff (by otype) hc₁).1 h₁
    obtain ⟨k₂, l₂⟩ := (bprf_iff (by otype) hc₂).1 h₂
    exact (bprf_iff (by otype) (by unfold mpX; otype)).2
      ⟨prf_mpH hys hc₁ hc₂ k₁ k₂, leafT_mpX hc₁ hc₂ l₁ l₂⟩
  · obtain ⟨z, bz, hz⟩ := hcl E.hasNat.toNatConsts.bzeroT
    obtain ⟨s, bs, hs⟩ := hcl E.hasNat.toNatConsts.bsuccT
    have ln := leafT_numCert (env := Incomplete.bounded X) (leafT_numT bz) (leafT_numT bs)
    refine ⟨z, s, fun {Γ ys P c a} hys hc ha h => ?_⟩
    obtain ⟨k, l⟩ := (bprf_iff (by otype) hc).1 h
    have hn : Tm (Incomplete.bounded X) Γ (numCert z s a) := by otype
    refine (bprf_iff (by otype) (by unfold mpX; otype)).2
      ⟨prf_allH (hz (Γ := [])).1 (hz (Γ := [])).2 (hs (Γ := [])).1 (hs (Γ := [])).2 hys hc ha k,
        leafT_mpX hc hn l ?_⟩
    have := Thm.allE (ln.weak0 (Γ := Γ)) ha
    simpa only [obj_simp] using this
  · intro Γ A B c₁ c₂ hB hc₁ hc₂ h₁ h₂
    obtain ⟨k₁, l₁⟩ := (bprf_iff (by otype) hc₁).1 h₁
    obtain ⟨k₂, l₂⟩ := (bprf_iff (by otype) hc₂).1 h₂
    have hp : Tm (Incomplete.bounded X) Γ (fldT 1 (jT c₁)) := by otype
    have hq : Tm (Incomplete.bounded X) Γ (fldT 1 (jT c₂)) := by otype
    refine (bprf_iff (by otype) (mpTTy hp hq hc₁ hc₂)).2 ⟨prf_mpT hB hc₁ hc₂ k₁ k₂, ?_⟩
    unfold Obj.mpT
    exact leafT_appT zeroTy (by otype) (by otype) hp hp hq hq hc₁ hc₂ l₁ l₂

end Incomplete.Obj
