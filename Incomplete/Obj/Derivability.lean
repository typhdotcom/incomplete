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
open VExpr Typing PR

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {T : PR}

/-- `provMC T P` at any arguments `[k, x]` is `Prf(⌜P⌝, k)`. -/
theorem ev_provM (hb : bnd T ≤ 2) {P k x : VExpr} (hk : Tm env Γ k) (hx : Tm env Γ x) :
    Thm env Γ (ev (provMC T P) [k, x] =ₒ prf T (numT (encExpr P)) k) := by
  orw [ev_push (f := provMC T P) rfl (by otype)]
  rw [ev_take 2 hb]
  simp only [List.take_succ_cons, List.take_zero, ev_numC_ctx]
  orefl

/-- A certificate of `P` proves `ProvC T P`. -/
theorem prov_intro {P k : VExpr} (hk : Tm env Γ k) (h : Thm env Γ (prf T (numT (encExpr P)) k =ₒ zero)) :
    Thm env Γ (ProvC T P) := by
  unfold ProvC
  refine Thm.exI (t := k) (by otype) hk ?_
  simp only [obj_simp]
  exact h

/-- **The graph lemma of `provMC T P`**: a zero of it gives `ProvC T P`. -/
theorem gp_prov (hb : bnd T ≤ 2) {P k x : VExpr} (hk : Tm env Γ k) (hx : Tm env Γ x) :
    Thm env Γ (imp (ev (provMC T P) [k, x] =ₒ zero) (ProvC T P)) := by
  ointro h
  orw [ev_provM hb (by otype) (by otype)] at h
  exact prov_intro (by otype) h

/-- **Internal Σ₁-completeness for `Prov`**: a code `σ` turns, provably, every certificate `k` of
`P` into a certificate `σ k` of `ProvC T P`. -/
theorem sigma_prov (hT : IsChecker env T) (P : VExpr) :
    ∃ σ : PR, Thm env [] (∀ₒ k, prf T (numT (encExpr P)) k =ₒ zero →ₒ
      prf T (numT (encExpr (ProvC T P))) (ev σ [k]) =ₒ zero) := by
  have hG : Thm env [] (allN 2 (imp ((valF (provMC T P) 2).inst zero 0) (ProvC T P))) := by
    rw [valF_fin_eq]
    exact allN_intro (env := env) 2 (Γ := []) (gp_prov hT.bnd (bvar_rep (by omega)) (bvar_rep (by omega)))
  exact sigma_of_fin hT (by simp only [obj_simp]) (Prov_closed T P) hG (fun hk => fn_provM hT.bnd hk)

/-- **D3**, internally. -/
theorem prov_prov (hT : IsChecker env T) (P : VExpr) :
    Thm env [] (imp (ProvC T P) (ProvC T (ProvC T P))) := by
  obtain ⟨σ, hσ⟩ := sigma_prov hT P
  ointro h
  unfold ProvC at h
  ocases h with hk
  generalize hΔ : [prf T (numT (encExpr P)) (.bvar 0) =ₒ zero, nat, ProvC T P] = Δ at hk ⊢
  have hkT : Tm env Δ (.bvar 1) := by subst hΔ; otype
  have hs := Thm.allE (hσ.weak0 (Γ := Δ)) (t := .bvar 1) hkT
  simp only [obj_simp] at hs
  exact prov_intro (by otype) (hs.mp hk)

/-- **D2**, in context, for closed `B`. -/
theorem prov_mp_ctx (hT : MpT env T) {A B : VExpr} (hB : B.ClosedN) (h1 : Thm env Γ (ProvC T (imp A B)))
    (h2 : Thm env Γ (ProvC T A)) : Thm env Γ (ProvC T B) := by
  refine Thm.exEHT (by otype) (by otype) h1 (fun hk1T hk1 => ?_)
  have h2' : Thm env ((prf T (numT (encExpr (imp A B))) (.bvar 0) =ₒ zero) :: nat :: Γ)
      (ProvC T A) := ((h2.weak (A := nat)).weak).cast (by simp only [obj_simp])
  refine Thm.exEHT (by otype) (by otype) h2' (fun hk2T hk2 => ?_)
  have hk1' := (hk1.weak (A := nat)).weak
    (A := prf T (numT (encExpr A)) (.bvar 0) =ₒ zero)
  simp only [obj_simp] at hk1' hk2 ⊢
  exact prov_intro (by otype) (hT hB (weakNat (weakNat hk1T)) hk2T hk1' hk2)

/-- **D2**, internally, for closed `B`. -/
theorem prov_mp (hT : MpT env T) {A B : VExpr} (hB : B.ClosedN) :
    Thm env [] (imp (ProvC T (imp A B)) (imp (ProvC T A) (ProvC T B))) := by
  ointro
  ointro
  exact prov_mp_ctx hT (A := A) hB ((Thm.hyp (.succ .zero)).cast (by simp only [obj_simp]))
    ((Thm.hyp .zero).cast (by simp only [obj_simp]))

/-- **D3**, in context. -/
theorem prov_prov_ctx (hT : IsChecker env T) {P : VExpr} (h : Thm env Γ (ProvC T P)) :
    Thm env Γ (ProvC T (ProvC T P)) :=
  (prov_prov hT P).weak0.mp h

/-- **Formalized Löb**, internally, for a closed proposition `P`. With
`X := ProvC T (ProvC T P → P)`, the theory proves `ProvC T (X → ProvC T P) → X → ProvC T P`: from
`X`, D3 gives `ProvC T X`, D2 `ProvC T (ProvC T P)`, and D2 at `X` itself `ProvC T P`. Löb's theorem
(`loeb_core`) at `X → ProvC T P` concludes. -/
theorem loeb_int (hT : IsChecker env T) {P : VExpr} (hPc : P.ClosedN) :
    Thm env [] (imp (ProvC T (imp (ProvC T P) P)) (ProvC T P)) := by
  generalize hX : ProvC T (imp (ProvC T P) P) = X
  have hXc : X.ClosedN := hX ▸ Prov_closed T _
  have hXT : env.HasType [] X (.sort .zero) := hX ▸ ProvTy T _
  have hQc : (imp X (ProvC T P)).ClosedN := by
    show VExpr.ClosedN (.forallE _ _)
    exact ⟨hXc, (Prov_closed T P).liftN⟩
  have hQT : env.HasType [] (imp X (ProvC T P)) (.sort .zero) := impTy hXT (ProvTy T P)
  have hL : Thm env [] (imp (ProvC T (imp X (ProvC T P))) (imp X (ProvC T P))) := by
    refine Thm.intro (ProvTy T _) ?_
    rw [hQc.lift_eq]
    refine Thm.intro (closedTy hXT) ?_
    rw [(Prov_closed T P).lift_eq]
    have hx : Thm env [X, ProvC T (imp X (ProvC T P))] X := (Thm.hyp .zero).cast hXc.lift_eq
    have hq : Thm env [X, ProvC T (imp X (ProvC T P))] (ProvC T (imp X (ProvC T P))) :=
      (Thm.hyp (.succ .zero)).cast (by rw [(Prov_closed T _).lift_eq, (Prov_closed T _).lift_eq])
    have hx' : Thm env [X, ProvC T (imp X (ProvC T P))] (ProvC T (imp (ProvC T P) P)) :=
      hx.cast hX.symm
    have hxx : Thm env [X, ProvC T (imp X (ProvC T P))] (ProvC T X) :=
      (prov_prov_ctx hT hx').cast (by rw [hX])
    have hpp := prov_mp_ctx hT.mpT (Prov_closed T P) hq hxx
    exact prov_mp_ctx hT.mpT hPc hx' hpp
  exact loeb_core hT hQc hQT (fun hk => fn_loebM_code hT.bnd hQc hk) hL

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
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  have hQc : Q.ClosedN := hQ.closedN hwf.ordered trivial
  have h : Thm env [] (imp (Prov T (imp P Q)) (imp (Prov T P) (Prov T Q))) :=
    prov_mp (env := env) (T := chkT T) (A := P) mpT_full hQc
  have hc : (imp (Prov T P) (Prov T Q)).ClosedN :=
    (impTy (env := env) (ProvTy' (Γ := []) T P) (ProvTy' T Q)).closedN.1
  rw [imp_eq_forallE hc, imp_eq_forallE hQc, imp_eq_forallE (Prov_closed' T Q)] at h
  exact h.provable

/-- **D3.** The theory proves `Prov T P → Prov T (Prov T P)`. -/
theorem prov_prov_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (P : VExpr) :
    Provable env (.forallE (Prov T P) (Prov T (Prov T P))) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  have h : Thm env [] (imp (Prov T P) (Prov T (Prov T P))) :=
    prov_prov (env := env) (IsChecker.full hT) P
  rw [imp_eq_forallE (Prov_closed' T _)] at h
  exact h.provable

/-- **Formalized Löb's theorem.** For a closed proposition `P`, the theory proves
`Prov T (Prov T P → P) → Prov T P`. -/
theorem loeb_formalized (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {P : VExpr}
    (hP : env.HasType 0 [] P (.sort .zero)) :
    Provable env (.forallE (Prov T (.forallE (Prov T P) P)) (Prov T P)) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  have hPc : P.ClosedN := hP.closedN hwf.ordered trivial
  have h : Thm env [] (imp (Prov T (imp (Prov T P) P)) (Prov T P)) :=
    loeb_int (env := env) (IsChecker.full hT) hPc
  rw [imp_eq_forallE hPc, imp_eq_forallE (Prov_closed' T P)] at h
  exact h.provable

end Incomplete
