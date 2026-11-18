import Incomplete.Obj.Loeb

/-!
# The derivability conditions and formalized Löb

For the provability sentence `Prov T P = ∃ k, Prf(⌜P⌝, k)`:

- **D1** is `prov_of_provable`.
- **D2** (`prov_mp_provable`): `Prov T (P → Q) → Prov T P → Prov T Q`. Internally, certificates
  `k₁` of `P → Q` and `k₂` of `P` give the `appDF` certificate `mpT … k₁ k₂` of `Q` (`prf_mpT`).
- **D3** (`prov_prov_provable`): `Prov T P → Prov T (Prov T P)`. `provM T P` at `0` and `k` is
  `Prf(⌜P⌝, k)`, and every zero of it gives `Prov T P` (`gp_prov`), so internal Σ₁-completeness
  (`sigma_of_fin`) yields a code `σ` with `∀ k, Prf(⌜P⌝, k) → Prf(⌜Prov T P⌝, σ k)`
  (`sigma_prov`): `σ k` is the certificate of the checker's evaluation at `k`.

**Formalized Löb** (`loeb_formalized`): `Prov T (Prov T P → P) → Prov T P`. For
`X := Prov T (Prov T P → P)`, D2 and D3 prove `Prov T (X → Prov T P) → X → Prov T P`, and Löb's
theorem gives `X → Prov T P`.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv PR

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {T : Tables}

/-- `provM T P` at any arguments `[k, x]` is `Prf(⌜P⌝, k)`. -/
theorem ev_provM {P k x : VExpr} (hk : Tm env Γ k) (hx : Tm env Γ x) :
    Thm env Γ (ev (provM T P) [k, x] =ₒ prfT T (numT (encExpr P)) k) := by
  orw [ev_push (f := provM T P) rfl (by otype)]
  rw [ev_take 2 (bnd_chkT T)]
  simp only [List.take_succ_cons, List.take_zero, ev_numC_ctx]
  orefl

/-- A certificate of `P` proves `Prov T P`. -/
theorem prov_intro {P k : VExpr} (hk : Tm env Γ k) (h : Thm env Γ (prfT T (numT (encExpr P)) k =ₒ zero)) :
    Thm env Γ (Prov T P) := by
  unfold Prov
  refine Thm.exI (t := k) (by otype) hk ?_
  simp only [obj_simp]
  exact h

/-- **The graph lemma of `provM T P`**: a zero of it gives `Prov T P`. -/
theorem gp_prov {P k x : VExpr} (hk : Tm env Γ k) (hx : Tm env Γ x) :
    Thm env Γ (imp (ev (provM T P) [k, x] =ₒ zero) (Prov T P)) := by
  ointro h
  orw [ev_provM (by otype) (by otype)] at h
  exact prov_intro (by otype) h

/-- **Internal Σ₁-completeness for `Prov`**: a code `σ` turns, provably, every certificate `k` of
`P` into a certificate `σ k` of `Prov T P`. -/
theorem sigma_prov (hT : TablesFor env T) (P : VExpr) :
    ∃ σ : PR, Thm env [] (∀ₒ k, prfT T (numT (encExpr P)) k =ₒ zero →ₒ
      prfT T (numT (encExpr (Prov T P))) (ev σ [k]) =ₒ zero) := by
  have hG : Thm env [] (allN 2 (imp ((valF (provM T P) 2).inst zero 0) (Prov T P))) := by
    rw [valF_fin_eq]
    exact allN_intro (env := env) 2 (Γ := []) (gp_prov (bvar_rep (by omega)) (bvar_rep (by omega)))
  exact sigma_of_fin hT (by simp only [obj_simp]) (Prov_closed T P) hG (fun hk => fn_provM hk)

/-- **D3**, internally. -/
theorem prov_prov (hT : TablesFor env T) (P : VExpr) :
    Thm env [] (imp (Prov T P) (Prov T (Prov T P))) := by
  obtain ⟨σ, hσ⟩ := sigma_prov hT P
  ointro h
  unfold Prov at h
  ocases h with hk
  generalize hΔ : [prfT T (numT (encExpr P)) (.bvar 0) =ₒ zero, nat, Prov T P] = Δ at hk ⊢
  have hkT : Tm env Δ (.bvar 1) := by subst hΔ; otype
  have hs := Thm.allE (hσ.weak0 (Γ := Δ)) (t := .bvar 1) hkT
  simp only [obj_simp] at hs
  exact prov_intro (by otype) (hs.mp hk)

/-- **D2**, in context, for closed `B`. -/
theorem prov_mp_ctx {A B : VExpr} (hB : B.ClosedN) (h1 : Thm env Γ (Prov T (imp A B)))
    (h2 : Thm env Γ (Prov T A)) : Thm env Γ (Prov T B) := by
  refine Thm.exEHT (by otype) (by otype) h1 (fun hk1T hk1 => ?_)
  have h2' : Thm env ((prfT T (numT (encExpr (imp A B))) (.bvar 0) =ₒ zero) :: nat :: Γ)
      (Prov T A) := ((h2.weak (A := nat)).weak).cast (by simp only [obj_simp])
  refine Thm.exEHT (by otype) (by otype) h2' (fun hk2T hk2 => ?_)
  have hk1' := (hk1.weak (A := nat)).weak
    (A := prfT T (numT (encExpr A)) (.bvar 0) =ₒ zero)
  simp only [obj_simp] at hk1' hk2 ⊢
  exact prov_intro (by otype) (prf_mpT hB (weakNat (weakNat hk1T)) hk2T hk1' hk2)

/-- **D2**, internally, for closed `B`. -/
theorem prov_mp {A B : VExpr} (hB : B.ClosedN) :
    Thm env [] (imp (Prov T (imp A B)) (imp (Prov T A) (Prov T B))) := by
  ointro
  ointro
  exact prov_mp_ctx (A := A) hB ((Thm.hyp (.succ .zero)).cast (by simp only [obj_simp]))
    ((Thm.hyp .zero).cast (by simp only [obj_simp]))

/-- **D3**, in context. -/
theorem prov_prov_ctx (hT : TablesFor env T) {P : VExpr} (h : Thm env Γ (Prov T P)) :
    Thm env Γ (Prov T (Prov T P)) :=
  (prov_prov hT P).weak0.mp h

/-- **Formalized Löb**, internally, for a closed proposition `P`. With
`X := Prov T (Prov T P → P)`, the theory proves `Prov T (X → Prov T P) → X → Prov T P`: from
`X`, D3 gives `Prov T X`, D2 `Prov T (Prov T P)`, and D2 at `X` itself `Prov T P`. Löb's theorem
(`loeb_core`) at `X → Prov T P` concludes. -/
theorem loeb_int (hT : TablesFor env T) {P : VExpr} (hPc : P.ClosedN) :
    Thm env [] (imp (Prov T (imp (Prov T P) P)) (Prov T P)) := by
  generalize hX : Prov T (imp (Prov T P) P) = X
  have hXc : X.ClosedN := hX ▸ Prov_closed T _
  have hXT : env.HasType 0 [] X (.sort .zero) := hX ▸ ProvTy T _
  have hQc : (imp X (Prov T P)).ClosedN := by
    show VExpr.ClosedN (.forallE _ _)
    exact ⟨hXc, (Prov_closed T P).liftN⟩
  have hQT : env.HasType 0 [] (imp X (Prov T P)) (.sort .zero) := impTy hXT (ProvTy T P)
  have hL : Thm env [] (imp (Prov T (imp X (Prov T P))) (imp X (Prov T P))) := by
    refine Thm.intro (ProvTy T _) ?_
    rw [hQc.lift_eq]
    refine Thm.intro (closedTy hXT) ?_
    rw [(Prov_closed T P).lift_eq]
    have hx : Thm env [X, Prov T (imp X (Prov T P))] X := (Thm.hyp .zero).cast hXc.lift_eq
    have hq : Thm env [X, Prov T (imp X (Prov T P))] (Prov T (imp X (Prov T P))) :=
      (Thm.hyp (.succ .zero)).cast (by rw [(Prov_closed T _).lift_eq, (Prov_closed T _).lift_eq])
    have hx' : Thm env [X, Prov T (imp X (Prov T P))] (Prov T (imp (Prov T P) P)) :=
      hx.cast hX.symm
    have hxx : Thm env [X, Prov T (imp X (Prov T P))] (Prov T X) :=
      (prov_prov_ctx hT hx').cast (by rw [hX])
    have hpp := prov_mp_ctx (Prov_closed T P) hq hxx
    exact prov_mp_ctx hPc hx' hpp
  exact loeb_core hT hQc hQT (fun hk => fn_loebM_code hQc hk) hL

end

end Incomplete.Obj

namespace Incomplete
open Lean4Lean Obj

theorem imp_eq_forallE {A B : VExpr} (hB : B.ClosedN) : Obj.imp A B = .forallE A B := by
  show VExpr.forallE A (B.liftN 1 0) = _; rw [hB.liftN_eq (Nat.zero_le _)]

/-- **D2.** For a closed proposition `Q`, the theory proves
`Prov T (P → Q) → Prov T P → Prov T Q`. -/
theorem prov_mp_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    {P Q : VExpr} (hQ : env.HasType 0 [] Q (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE P Q)) (.forallE (Prov T P) (Prov T Q))) := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have hQc : Q.ClosedN := hQ.closedN hwf.ordered trivial
  have h := prov_mp (env := env) (T := T) (A := P) hQc
  have hc : (imp (Prov T P) (Prov T Q)).ClosedN :=
    (impTy (ProvTy (Γ := []) T P) (ProvTy T Q)).closedN hwf.ordered trivial
  rw [imp_eq_forallE hc, imp_eq_forallE hQc, imp_eq_forallE (Prov_closed T Q)] at h
  exact h.provable

/-- **D3.** The theory proves `Prov T P → Prov T (Prov T P)`. -/
theorem prov_prov_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (P : VExpr) :
    Provable env (.forallE (Prov T P) (Prov T (Prov T P))) := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have h := prov_prov hT P
  rw [imp_eq_forallE (Prov_closed T _)] at h
  exact h.provable

/-- **Formalized Löb's theorem.** For a closed proposition `P`, the theory proves
`Prov T (Prov T P → P) → Prov T P`. -/
theorem loeb_formalized (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr}
    (hP : env.HasType 0 [] P (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE (Prov T P) P)) (Prov T P)) := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have hPc : P.ClosedN := hP.closedN hwf.ordered trivial
  have h := loeb_int hT hPc
  rw [imp_eq_forallE hPc, imp_eq_forallE (Prov_closed T P)] at h
  exact h.provable

end Incomplete
