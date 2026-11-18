import Incomplete.Sentences

/-!
# Induction in the object theory

`Nat.rec.{0}` at a closed motive `M : Nat → Prop` proves `∀ n, M n` from `M 0` and the step
(`recPT`). Two consequences are what Rosser's argument needs of the object theory: a property
of every numeral and of every `q + y` holds of every number (`forall_of_numerals`), and
`Nat.rec a (fun _ _ => 1) v` is nonzero when `v` is (`nonzero_natRec`).
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

/-- `Nat.rec.{0} M z s n`. -/
def recP (M z s n : VExpr) : VExpr := .appN (.const ``Nat.rec [.zero]) [M, z, s, n]

/-- The type of the step of an induction with motive `M`. -/
def stepTy (M : VExpr) : VExpr :=
  .forallE nat (.forallE (.app M (.bvar 0)) (.app M (.app succ (.bvar 1))))

/-- `n ≠ 0`, as `isZero n → False`. -/
def nonzero (n : VExpr) : VExpr := .forallE (isZero n) falseS

/-- `fun _ _ => 1`. -/
def oneF : VExpr := .lam nat (.lam nat (lit 1))

/-- `succ (succ ⋯ y)`, `q` times. -/
def succIter : Nat → VExpr → VExpr
  | 0, y => y
  | q + 1, y => .app succ (succIter q y)

theorem succIter_succ : ∀ q y, succIter q (.app succ y) = succIter (q + 1) y
  | 0, _ => rfl
  | q + 1, y => by rw [succIter, succIter_succ q y]; rfl

theorem succIter_zero : ∀ q, succIter q zero = lit q
  | 0 => rfl
  | q + 1 => by rw [succIter, succIter_zero q]; rfl

@[simp] theorem succIter_inst (a : VExpr) (k : Nat) : ∀ q y,
    (succIter q y).inst a k = succIter q (y.inst a k)
  | 0, _ => rfl
  | q + 1, y => by simp [succIter, VExpr.inst, succIter_inst a k q y]

theorem Inert.ofClosed {M : VExpr} (h : M.ClosedN) : Inert M :=
  ⟨fun _ _ => h.liftN_eq (Nat.zero_le _), fun _ _ => h.instN_eq (Nat.zero_le _), fun σ => by
    rw [h.subst_congr (σ' := .id) (fun _ h => absurd h (Nat.not_lt_zero _)), subst_id]⟩

theorem Inert.oneF : Inert oneF :=
  ⟨fun _ _ => by simp [Incomplete.oneF, VExpr.liftN, (Inert.lit 1).liftN],
   fun _ _ => by simp [Incomplete.oneF, VExpr.inst, (Inert.lit 1).inst],
   fun _ => by simp [Incomplete.oneF, VExpr.subst, (Inert.lit 1).subst]⟩

@[simp] theorem natRec_inst (A z s n a : VExpr) (k : Nat) :
    (natRec A z s n).inst a k = natRec (A.inst a (k + 1)) (z.inst a k) (s.inst a k) (n.inst a k) :=
  rfl

@[simp] theorem isZero_instN (n a : VExpr) (k : Nat) :
    (isZero n).inst a k = isZero (n.inst a k) := rfl

@[simp] theorem nonzero_inst (n a : VExpr) (k : Nat) :
    (nonzero n).inst a k = nonzero (n.inst a k) := rfl

section
variable {env : VEnv} {Γ : List VExpr}

/-- A proposition quantified over anything is a proposition. -/
theorem forallE_prop {A B : VExpr} {u : VLevel}
    (hA : env.HasType 0 Γ A (.sort u)) (hB : env.HasType 0 (A :: Γ) B (.sort .zero))
    (hu : u.WF 0 := by trivial) :
    env.HasType 0 Γ (.forallE A B) (.sort .zero) :=
  .defeqDF (.sortDF (l := .imax u .zero) ⟨hu, trivial⟩ trivial (VLevel.equiv_def.2 fun _ => by
    simp [VLevel.eval, Lean.Nat.imax])) (HasType.forallE hA hB)

variable (H : HasNat env)
include H

theorem isZeroT {n : VExpr} (hn : env.HasType 0 Γ n nat) :
    env.HasType 0 Γ (isZero n) (.sort .zero) :=
  H.natRecT Inert.sort (fun _ => .sort trivial) trueT (isZeroStepT H) hn

theorem nonzeroT {n : VExpr} (hn : env.HasType 0 Γ n nat) :
    env.HasType 0 Γ (nonzero n) (.sort .zero) :=
  forallE_prop (isZeroT H hn) falseT

theorem oneFT : env.HasType 0 Γ oneF (.forallE nat (.forallE nat nat)) :=
  .lam H.natT (.lam H.natT (H.litT 1))

theorem succIterT {y : VExpr} (hy : env.HasType 0 Γ y nat) :
    ∀ q, env.HasType 0 Γ (succIter q y) nat
  | 0 => hy
  | q + 1 => .app' H.succT (succIterT hy q) rfl

variable (henv : env.Ordered)
include henv

/-- **Induction into `Prop`**, at a closed motive. -/
theorem recPT {M z s n : VExpr} (hM : env.HasType 0 [] M (.forallE nat (.sort .zero)))
    (hz : env.HasType 0 Γ z (.app M zero)) (hs : env.HasType 0 Γ s (stepTy M))
    (hn : env.HasType 0 Γ n nat) : env.HasType 0 Γ (recP M z s n) (.app M n) := by
  have hI := Inert.ofClosed (hM.closedN henv trivial)
  have h0 : env.HasType 0 Γ (.const ``Nat.rec [.zero])
      (.forallE (.forallE nat (.sort .zero)) (.forallE (.app (.bvar 0) zero)
        (.forallE (.forallE nat (.forallE (.app (.bvar 2) (.bvar 0))
          (.app (.bvar 3) (.app succ (.bvar 1))))) (.forallE nat (.app (.bvar 3) (.bvar 0)))))) :=
    .const' H.hRec (by simp [VLevel.WF]) rfl rfl
  have h1 := HasType.app' h0 (hM.weak0 henv)
    (B' := .forallE (.app M zero) (.forallE (stepTy M) (.forallE nat (.app M (.bvar 0)))))
    (by simp [VExpr.inst, instVar, stepTy, hI.liftN])
  have h2 := HasType.app' h1 hz (B' := .forallE (stepTy M) (.forallE nat (.app M (.bvar 0))))
    (by simp [VExpr.inst, instVar, stepTy, hI.inst])
  have h3 := HasType.app' h2 hs (B' := .forallE nat (.app M (.bvar 0)))
    (by simp [VExpr.inst, instVar, hI.inst])
  exact HasType.app' h3 hn (by simp [VExpr.inst, instVar, hI.inst])

/-- `isZero (succ n) ≡ False`. -/
theorem isZero_succ (hΓ : OnCtx Γ (env.IsType 0)) {n : VExpr} (hn : env.HasType 0 Γ n nat) :
    env.IsDefEq 0 Γ (isZero (.app succ n)) falseS (.sort .zero) := by
  have h1 := H.iota_succ' henv hΓ Inert.sort (fun _ => .sort trivial) trueT (isZeroStepT H) hn
  have b1 : env.IsDefEq 0 Γ (.app (.lam nat (.lam (.sort .zero) falseS)) n)
      (.lam (.sort .zero) falseS) (.forallE (.sort .zero) (.sort .zero)) :=
    IsDefEq.beta (HasType.lam (HasType.sort (l := .zero) trivial) falseT) hn
  have b2 : env.IsDefEq 0 Γ (.app (.lam (.sort .zero) falseS) (isZero n)) falseS (.sort .zero) :=
    IsDefEq.beta falseT (isZeroT H hn)
  exact h1.trans ((IsDefEq.appDF b1 (isZeroT H hn)).trans b2)

theorem isZero_lit_succ (k : Nat) :
    env.IsDefEq 0 Γ (isZero (lit (k + 1))) falseS (.sort .zero) :=
  (isZero_succ H henv (Γ := []) trivial (H.litT k)).weak0 henv

theorem isZero_zero : env.IsDefEq 0 Γ (isZero zero) trueS (.sort .zero) :=
  (H.iota_zero henv Inert.sort (fun _ => .sort trivial) trueT (isZeroStepT H)).weak0 henv

/-- A nonzero numeral is provably nonzero. -/
theorem nonzero_lit {k : Nat} (hk : k ≠ 0) :
    env.HasType 0 Γ (.lam falseS (.bvar 0)) (nonzero (lit k)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have : env.HasType 0 Γ (.lam falseS (.bvar 0)) (.forallE falseS falseS) :=
    HasType.lam falseT (.bvar .zero)
  exact (IsDefEq.forallEDF (isZero_lit_succ H henv k) falseT).symm.defeq this

/-- `Nat.rec a (fun _ _ => 1) (succ v) ≡ 1`. -/
theorem natRec_oneF_succ (hΓ : OnCtx Γ (env.IsType 0)) {a v : VExpr}
    (ha : env.HasType 0 Γ a nat) (hv : env.HasType 0 Γ v nat) :
    env.IsDefEq 0 Γ (natRec nat a oneF (.app succ v)) (lit 1) nat := by
  have hr := H.natRecT Inert.nat (fun _ => H.natT) ha (oneFT H) hv
  have h1 := H.iota_succ' henv hΓ Inert.nat (fun _ => H.natT) ha (oneFT H) hv
  have b1 : env.IsDefEq 0 Γ (.app oneF v) (.lam nat (lit 1)) (.forallE nat nat) := by
    have := IsDefEq.beta (HasType.lam H.natT (H.litT 1 (Γ := nat :: nat :: Γ))) hv
    simpa [oneF, VExpr.inst, (Inert.lit 1).inst] using this
  have b2 : env.IsDefEq 0 Γ (.app (.lam nat (lit 1)) (natRec nat a oneF v)) (lit 1) nat := by
    have := IsDefEq.beta (H.litT 1 (Γ := nat :: Γ)) hr
    simpa [(Inert.lit 1).inst] using this
  exact h1.trans ((IsDefEq.appDF b1 hr).trans b2)

/-- The body of the motive of `nonzero_natRec`. -/
def nzBody : VExpr :=
  .forallE nat (.forallE (nonzero (.bvar 1)) (nonzero (natRec nat (.bvar 1) oneF (.bvar 2))))

omit H henv in
theorem nzBody_inst (n : VExpr) : nzBody.inst n =
    .forallE nat (.forallE (nonzero n.lift) (nonzero (natRec nat (.bvar 1) oneF (n.liftN 2)))) := by
  simp [nzBody, VExpr.inst, instVar, Inert.oneF.inst, nat, VExpr.lift]

omit henv in
theorem nzBodyT : env.HasType 0 (nat :: Γ) nzBody (.sort .zero) :=
  forallE_prop H.natT (forallE_prop (nonzeroT H (.bvar (.succ .zero))) (nonzeroT H
    (H.natRecT Inert.nat (fun _ => H.natT) (.bvar (.succ .zero)) (oneFT H)
      (.bvar (.succ (.succ .zero))))))

/-- **A nonzero value stays nonzero**: `∀ v a, v ≠ 0 → Nat.rec a (fun _ _ => 1) v ≠ 0`. -/
theorem nonzero_natRec : ∃ p, env.HasType 0 [] p (.forallE nat nzBody) := by
  have hM : env.HasType 0 [] (.lam nat nzBody) (.forallE nat (.sort .zero)) :=
    .lam H.natT (nzBodyT H)
  have mapp : ∀ {Γ n}, env.HasType 0 Γ n nat →
      env.IsDefEq 0 Γ (.app (.lam nat nzBody) n) (nzBody.inst n) (.sort .zero) :=
    fun hn => IsDefEq.beta (nzBodyT H) hn
  -- zero: `v = 0` contradicts `v ≠ 0`
  have hz : env.HasType 0 [] (.lam nat (.lam (nonzero zero)
      (.lam (isZero (natRec nat (.bvar 1) oneF zero)) (.app (.bvar 1) trueI))))
      (.app (.lam nat nzBody) zero) := by
    refine (mapp H.zeroT).symm.defeq ?_
    rw [nzBody_inst]
    refine .lam H.natT (.lam (nonzeroT H H.zeroT) (.lam (isZeroT H ?_) ?_))
    · exact H.natRecT Inert.nat (fun _ => H.natT) (.bvar (.succ .zero)) (oneFT H) H.zeroT
    · exact .app' (.bvar (.succ .zero)) ((isZero_zero H henv).symm.defeq trueI_T) rfl
  -- successor: `Nat.rec a (fun _ _ => 1) (succ v) ≡ 1`
  have hs : env.HasType 0 [] (.lam nat (.lam (.app (.lam nat nzBody) (.bvar 0))
      (.lam nat (.lam (nonzero (.app succ (.bvar 2))) (.lam falseS (.bvar 0))))))
      (stepTy (.lam nat nzBody)) := by
    have hm0 : env.HasType 0 [nat] (.app (.lam nat nzBody) (.bvar 0)) (.sort .zero) :=
      .app' (hM.weak0 henv) (.bvar .zero) rfl
    have hΓ : OnCtx [nonzero (.app succ (.bvar 2)), nat, .app (.lam nat nzBody) (.bvar 0), nat]
        (env.IsType 0) :=
      ⟨⟨⟨⟨trivial, _, H.natT⟩, _, hm0⟩, _, H.natT⟩, _,
        nonzeroT H (.app' H.succT (.bvar (.succ (.succ .zero))) rfl)⟩
    have hv : env.HasType 0 [nonzero (.app succ (.bvar 2)), nat, .app (.lam nat nzBody) (.bvar 0),
        nat] (.bvar 3) nat := .bvar (.succ (.succ (.succ .zero)))
    have hc := (isZero_congr H (natRec_oneF_succ H henv hΓ (.bvar (.succ .zero)) hv)).trans
      (isZero_lit_succ H henv 0)
    refine .lam H.natT (.lam hm0 ?_)
    refine (mapp (.app' H.succT (.bvar (.succ .zero)) rfl)).symm.defeq ?_
    rw [nzBody_inst]
    refine .lam H.natT (.lam (nonzeroT H (.app' H.succT (.bvar (.succ (.succ .zero))) rfl)) ?_)
    exact (IsDefEq.forallEDF hc falseT).symm.defeq (HasType.lam falseT (.bvar .zero))
  have h0 : env.HasType 0 [nat] (.bvar 0) nat := .bvar .zero
  have h := recPT H henv hM (hz.weak0 henv) (hs.weak0 henv) h0
  have h' := (mapp h0).defeq h
  rw [nzBody_inst] at h'
  exact ⟨_, .lam H.natT h'⟩

/-- `nonzero_natRec` at open terms. -/
theorem nonzero_natRec_app {v a p : VExpr} (hv : env.HasType 0 Γ v nat)
    (ha : env.HasType 0 Γ a nat) (hp : env.HasType 0 Γ p (nonzero v)) :
    ∃ p', env.HasType 0 Γ p' (nonzero (natRec nat a oneF v)) := by
  obtain ⟨L, hL⟩ := nonzero_natRec H henv
  have h1 := HasType.app' (hL.weak0 henv) hv rfl
  rw [nzBody_inst] at h1
  have h2 := HasType.app' h1 ha rfl
  simp only [VExpr.inst, nonzero_inst, natRec_inst, instVar, inst_liftN_lo, liftN_zero,
    Inert.oneF.inst, Inert.nat.inst] at h2
  exact ⟨_, HasType.app' h2 hp (by simp [inst_lift, Inert.oneF.inst, Inert.nat.inst])⟩

/-- **A property of every numeral and of every `q + y` holds of every number**, at a closed
motive. -/
theorem forall_of_numerals {M : VExpr} (hM : env.HasType 0 [] M (.forallE nat (.sort .zero)))
    (he : ∀ j, ∃ p, env.HasType 0 [] p (.app M (lit j))) :
    ∀ q, (∃ t, env.HasType 0 [] t (.forallE nat (.app M (succIter q (.bvar 0))))) →
      ∃ p, env.HasType 0 [] p (.forallE nat (.app M (.bvar 0)))
  | 0, ht => ht
  | q + 1, ⟨t, ht⟩ => by
    have hI := Inert.ofClosed (hM.closedN henv trivial)
    have hb : env.HasType 0 [nat] (.app M (succIter q (.bvar 0))) (.sort .zero) :=
      .app' (hM.weak0 henv) (succIterT H (.bvar .zero) q) rfl
    have hM' : env.HasType 0 [] (.lam nat (.app M (succIter q (.bvar 0))))
        (.forallE nat (.sort .zero)) := .lam H.natT hb
    have mapp : ∀ {Γ n}, env.HasType 0 Γ n nat →
        env.IsDefEq 0 Γ (.app (.lam nat (.app M (succIter q (.bvar 0)))) n)
          (.app M (succIter q n)) (.sort .zero) := by
      intro Γ n hn
      have := IsDefEq.beta (Γ := Γ)
        (HasType.app' (hM.weak0 henv) (succIterT H (.bvar .zero) q) rfl) hn
      simpa [VExpr.inst, hI.inst] using this
    obtain ⟨e, heq⟩ := he q
    have hz : env.HasType 0 [nat] e (.app (.lam nat (.app M (succIter q (.bvar 0)))) zero) :=
      (mapp H.zeroT).symm.defeq (by rw [succIter_zero]; exact heq.weak0 henv)
    have hs : env.HasType 0 [nat] (.lam nat (.lam (.app (.lam nat (.app M (succIter q (.bvar 0))))
        (.bvar 0)) (.app t (.bvar 1)))) (stepTy (.lam nat (.app M (succIter q (.bvar 0))))) := by
      refine .lam H.natT (.lam (.app' (hM'.weak0 henv) (.bvar .zero) rfl) ?_)
      refine (mapp (.app' H.succT (.bvar (.succ .zero)) rfl)).symm.defeq ?_
      rw [succIter_succ]
      exact .app' (ht.weak0 henv) (.bvar (.succ .zero)) (by simp [VExpr.inst, hI.inst])
    have h0 : env.HasType 0 [nat] (.bvar 0) nat := .bvar .zero
    have h := (mapp h0).defeq (recPT H henv hM' hz hs h0)
    exact forall_of_numerals hM he q ⟨_, .lam H.natT h⟩

end

end Incomplete
