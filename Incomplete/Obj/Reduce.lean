import Incomplete.Obj.Template

/-!
# The second theorem from internal Σ₁-completeness for the diagonal machine

`Con T` and `G0 T` read through the checker: `conM T` at `0` and `k` is `Prf(⌜⊥⌝, k)`
(`fn_conM`), and `dg T` at its own code and `k` is `Prf(⌜G0 T⌝, k)` (`fn_dg`). Given a code `σ`
with, internally, `∀ k, Prf(⌜G0 T⌝, k) → Prf(⌜halts (dg T) ⌜dg T⌝⌝, σ k)`, a proof `k` of `G0 T`
and the certificate `σ k` of `G0 T → ⊥` combine by modus ponens into a certificate of `⊥`, which
`Con T` refutes; so the theory proves `Con T → G0 T` (`con_imp_G0`), and the second theorem
follows (`second_of_sigma`).
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr Typing PR

/-- The diagonal sentence's number, as `diagC` assembles it from the code `x`. -/
noncomputable def diagT (x : VExpr) : VExpr :=
  tagT 7 5 (pair (numT (encExpr nat)) (tagT 7 5 (pair
    (tagT 7 3 (pair (numT (encExpr (.appN (.const ``Nat.rec [.succ .zero])
      [motive (.sort .zero), trueS, .lam nat (.lam (.sort .zero) falseS)])))
      (tagT 7 3 (pair (tagT 7 3 (pair x (litT x))) (numT (encExpr (.bvar 0)))))))
    (numT (encExpr falseS)))))

theorem bnd_chkT (T : Tables) : bnd (chkT T) ≤ 2 := bnd_chkC T _

@[obj_simp] theorem isZero_liftN {n : VExpr} {m k : Nat} : (isZero n).liftN m k = isZero (n.liftN m k) :=
  rfl
@[obj_simp] theorem isZero_inst' {n e : VExpr} {k : Nat} : (isZero n).inst e k = isZero (n.inst e k) :=
  rfl

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {k x : VExpr} {T : Tables}

theorem diagTTy (hx : Tm env Γ x) : Tm env Γ (diagT x) := by unfold diagT; otype

theorem isZeroTy (hx : Tm env Γ x) : env.HasType Γ (isZero x) (.sort .zero) := isZeroT hx

end

macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine diagTTy ?_); otype))
macro_rules | `(tactic| otype_rules) => `(tactic| ((with_reducible refine isZeroTy ?_); otype))

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {k x : VExpr} {T : Tables}

theorem ev_diagC (hk : Tm env Γ k) (hx : Tm env Γ x) : Thm env Γ (ev diagC [k, x] =ₒ diagT x) := by
  simp only [diagC, diagT]
  orw [ev_tagC (by otype), ev_cpair (by otype), ev_tagC (by otype), ev_cpair (by otype),
    ev_tagC (by otype), ev_cpair (by otype), ev_tagC (by otype), ev_cpair (by otype),
    ev_tagC (by otype), ev_cpair (by otype), ev_push rfl (by otype)]
  rw [ev_take 1 bnd_litC]
  simp only [ev_numC_ctx, List.take_succ_cons, List.take_zero]
  orefl

/-- The diagonal sentence of the code `d`, at any first argument. -/
theorem ev_diagC_lit (hk : Tm env Γ k) (d : Nat) :
    Thm env Γ (ev diagC [k, lit d] =ₒ numT (diagNum d d)) := by
  have h := ev_lits (env := env) (Γ := Γ) diagC [0, d]
  rw [eval_diagC] at h
  simp only [List.map_cons, List.map_nil, lit_zero, List.getD_cons_succ, List.getD_cons_zero] at h
  orw [ev_diagC hk (litTy d), ← ev_diagC zeroTy (litTy d), h, numT_lit]

theorem fn_conM (hk : Tm env Γ k) :
    Thm env Γ (app2 (fn (conM T)) (lit 0) k =ₒ prfT T (numT (encExpr falseS)) k) := by
  orw [fn_ev zeroTy hk, ev_push (f := conM T) rfl (by otype)]
  rw [ev_take 2 (bnd_chkT T), ev_numC_ctx]
  simp only [List.take_succ_cons, List.take_zero]
  orefl

theorem fn_dg (hk : Tm env Γ k) (d : Nat) :
    Thm env Γ (app2 (fn (dg T)) (lit d) k =ₒ prfT T (numT (diagNum d d)) k) := by
  orw [fn_ev (litTy d) hk, ev_push (f := dg T) rfl (by otype)]
  rw [ev_take 2 (bnd_chkT T)]
  simp only [List.take_succ_cons, List.take_zero]
  orw [ev_diagC_lit hk d]

/-- `dg T` at its own code and `k` is `Prf(⌜G0 T⌝, k)`. -/
theorem fn_dg_code (hk : Tm env Γ k) :
    Thm env Γ (app2 (fn (dg T)) (lit (dg T).code) k =ₒ prfT T (numT (encExpr (G0 T))) k) := by
  have h := fn_dg (T := T) hk (dg T).code
  rw [diagNum_code] at h
  exact h

/-! ### `isZero` -/

theorem isZero_of_eq_zero (hx : Tm env Γ x) (h : Thm env Γ (x =ₒ zero)) : Thm env Γ (isZero x) := by
  have hM : env.HasType (nat :: Γ) (isZero (.bvar 0)) (.sort .zero) := isZeroT (.bvar .zero)
  have h0 : Thm env Γ (isZero zero) := ⟨_, (isZero_zero (env := env) (Γ := Γ)).symm.defeq trueI_T⟩
  have h1 := Thm.subst hM (Thm.symm hx zeroTy h) zeroTy hx (h0.cast (by simp only [obj_simp]))
  simp only [obj_simp] at h1
  exact h1

theorem eq_zero_of_isZero (hx : Tm env Γ x) (h : Thm env Γ (isZero x)) : Thm env Γ (x =ₒ zero) := by
  have hM : ∀ {Δ : List VExpr}, env.HasType (nat :: Δ) (isZero (.bvar 0)) (.sort .zero) :=
    isZeroT (.bvar .zero)
  ocases (zero_or_succ (n := x) hx) with hz hs
  · exact hz
  · ocases hs with m hm
    oexfalso
    olift h
    have h1 := Thm.subst hM hm (by otype) (by otype) (h.cast (by simp only [obj_simp]))
    simp only [obj_simp] at h1
    exact h1.conv (isZero_succ' mT)

end

/-! ### `Con → G0` -/

theorem falseS_closed : falseS.ClosedN := ⟨trivial, Nat.zero_lt_one⟩

theorem G0_eq (T : Tables) : G0 T =
    all (imp (isZero (app2 (fn (dg T)) (lit (dg T).code) (.bvar 0))) falseS) := rfl

theorem Con_eq (T : Tables) : Con T =
    all (imp (isZero (app2 (fn (conM T)) (lit 0) (.bvar 0))) falseS) := rfl

theorem halts_eq (f : PR) (n : Nat) : halts f n = imp (notHalts f n) falseS := rfl

section
variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr} {T : Tables}

/-- **Internal modus ponens on proofs**, for closed `B`: proofs `c₁` of `A → B` and `c₂` of `A`
give the proof `mpT A B p q c₁ c₂` of `B`, with `p` and `q` the terms they prove. -/
theorem prf_mpT {A B c₁ c₂ : VExpr} (hB : B.ClosedN) (hc₁ : Tm env Γ c₁) (hc₂ : Tm env Γ c₂)
    (h₁ : Thm env Γ (prfT T (numT (encExpr (imp A B))) c₁ =ₒ zero))
    (h₂ : Thm env Γ (prfT T (numT (encExpr A)) c₂ =ₒ zero)) :
    Thm env Γ (prfT T (numT (encExpr B)) (mpT A B (fldT 1 (jT c₁)) (fldT 1 (jT c₂)) c₁ c₂) =ₒ
      zero) := by
  have hpT : Tm env Γ (fldT 1 (jT c₁)) := by otype
  have hqT : Tm env Γ (fldT 1 (jT c₂)) := by otype
  obtain ⟨k₁, j₁⟩ := prfT_inv (by otype) hc₁ h₁
  obtain ⟨k₂, j₂⟩ := prfT_inv (by otype) hc₂ h₂
  have hm := certT_mp (A := A) (B := B) rfl hB hpT hqT hc₁ hc₂ k₁ j₁ k₂ j₂
  have jm := jT_mp (A := A) hB hpT hqT hc₁ hc₂
  exact prfT_of_cert (by otype) (mpTTy hpT hqT hc₁ hc₂) (by otype) hm jm

end

section
variable {env : Typing} [E : ObjEnv env] {T : Tables} {σ cm f : PR} {d : Nat} {A : VExpr}

/-- The argument of `con_imp_G0` over arbitrary codes `cm` and `f`, which `Prf` reads: if
`cm` at `0` reads `Prf(⌜⊥⌝, ·)`, `f` at `d` reads `Prf(⌜A⌝, ·)`, and the theory proves
`∀ k, Prf(⌜A⌝, k) → Prf(⌜A → ⊥⌝, σ k)`, then it proves that `cm` never halting on `0` implies
`f` never halting on `d`. -/
theorem con_imp_of_prf
    (hcm : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn cm) (lit 0) k =ₒ prfT T (numT (encExpr falseS)) k))
    (hf : ∀ {Γ : List VExpr} {k : VExpr}, Tm env Γ k →
      Thm env Γ (app2 (fn f) (lit d) k =ₒ prfT T (numT (encExpr A)) k))
    (hσ : Thm env [] (∀ₒ k, prfT T (numT (encExpr A)) k =ₒ zero →ₒ
      prfT T (numT (encExpr (imp A falseS))) (ev σ [k]) =ₒ zero)) :
    Thm env [] (imp (all (imp (isZero (app2 (fn cm) (lit 0) (.bvar 0))) falseS))
      (all (imp (isZero (app2 (fn f) (lit d) (.bvar 0))) falseS))) := by
  ointro hcon
  ointro
  ointro hz
  olift hcon
  generalize hΔ : [isZero (app2 (fn f) (lit d) (.bvar 0)), nat,
    all (imp (isZero (app2 (fn cm) zero (.bvar 0))) falseS)] = Δ at hz hcon ⊢
  have hkT : Tm env Δ (.bvar 1) := by subst hΔ; otype
  have hz' := eq_zero_of_isZero (by otype) hz
  orw [hf hkT] at hz'
  have hk := Thm.allE (hσ.weak0 (Γ := Δ)) (t := .bvar 1) hkT
  simp only [obj_simp] at hk
  have hk := hk.mp hz'
  have hsT : Tm env Δ (ev σ [.bvar 1]) := by otype
  have hf' := prf_mpT falseS_closed hsT hkT hk hz'
  have hmT : Tm env Δ (mpT A falseS (fldT 1 (jT (ev σ [.bvar 1]))) (fldT 1 (jT (.bvar 1)))
      (ev σ [.bvar 1]) (.bvar 1)) := mpTTy (by otype) (by otype) hsT hkT
  orw [← hcm hmT] at hf'
  have hc := Thm.allE hcon (t := mpT A falseS (fldT 1 (jT (ev σ [.bvar 1]))) (fldT 1 (jT (.bvar 1)))
    (ev σ [.bvar 1]) (.bvar 1)) hmT
  simp only [obj_simp] at hc
  exact hc.mp (isZero_of_eq_zero (by otype) hf')

/-- **`Con → G0`, from internal Σ₁-completeness for the diagonal machine.** -/
theorem con_imp_G0
    (hσ : Thm env [] (∀ₒ k, prfT T (numT (encExpr (G0 T))) k =ₒ zero →ₒ
      prfT T (numT (encExpr (halts (dg T) (dg T).code))) (ev σ [k]) =ₒ zero)) :
    Thm env [] (imp (Con T) (G0 T)) := by
  rw [Con_eq, G0_eq]
  exact con_imp_of_prf (fun hk => fn_conM hk) (fun hk => fn_dg_code hk) hσ

end

theorem G0_closed {env : Typing} [E : ObjEnv env] (T : Tables) : (G0 T).ClosedN :=
  (notHalts_prop E.hasNat E.ordered _ _).closedN E.ordered trivial

/-- **The second theorem, from internal Σ₁-completeness for the diagonal machine.** If for some
code `σ` the theory proves `∀ k, Prf(⌜G0 T⌝, k) → Prf(⌜halts (dg T) ⌜dg T⌝⌝, σ k)` and is
consistent, it does not prove `Con T`. -/
theorem second_of_sigma {env : VEnv} [E : ObjEnv env] {T : Tables} (hT : TablesFor env T) {σ : PR}
    (hσ : Thm env [] (∀ₒ k, prfT T (numT (encExpr (G0 T))) k =ₒ zero →ₒ
      prfT T (numT (encExpr (halts (dg T) (dg T).code))) (ev σ [k]) =ₒ zero))
    (hC : Consistent env) : ¬Provable env (Con T) := by
  have h := (con_imp_G0 hσ).provable
  have e : imp (Con T) (G0 T) = .forallE (Con T) (G0 T) := by
    show VExpr.forallE _ ((G0 T).liftN 1 0) = _
    rw [(G0_closed (env := env) T).liftN_eq (Nat.zero_le _)]
  rw [e] at h
  exact second_of_internal E.hasNat E.ordered hT h hC

end Incomplete.Obj
