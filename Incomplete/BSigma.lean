import Incomplete.BArith

/-!
# Σ₁-completeness in the fragment

The adequacy of `PR.tr` and the proof of a true `halts` sentence (`Adequacy.lean`,
`Sentences.lean`) go through in `BDefEq`: they form only `Prop` and `Type`, quantify only over
`Nat` and propositions, and use `Nat.rec` at `Type`.
-/

namespace Incomplete
open Lean4Lean
open VExpr VEnv

section
variable {env : VEnv} (H : HasNat env) (henv : env.Ordered)
include H henv

theorem PR.btrT : ∀ (f : PR) {Γ : List VExpr} {σ : Subst}, (∀ i, BDefEq env Γ (σ i) (σ i) nat) →
    BDefEq env Γ (f.tr.subst σ) (f.tr.subst σ) nat
  | .zero, _, _, _ => H.bzeroT
  | .var i, _, _, hσ => hσ i
  | .succ f, _, _, hσ => .app' H.bsuccT (f.btrT hσ) rfl
  | .push h g, Γ, σ, hσ => by
    refine .app' (.lamDF H.bnatT (g.btrT ?_)) (h.btrT hσ) rfl
    intro i; cases i with
    | zero => exact .bvar .zero
    | succ i => exact (hσ i).weak henv
  | .prec g h, Γ, σ, hσ => by
    refine H.bnatRecT Inert.nat (fun _ => H.bnatT) ?_ ?_ (hσ 0)
    · rw [lift_subst]; exact g.btrT fun i => hσ (i + 1)
    · refine .lamDF H.bnatT (.lamDF H.bnatT ?_)
      rw [liftN_subst_eq]
      refine h.btrT fun i => ?_
      match i with
      | 0 => exact .bvar .zero
      | 1 => exact .bvar (.succ .zero)
      | i + 2 =>
        have := ((hσ (i + 1)).weak henv (B := nat)).weak henv (B := nat)
        have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
        simp only [shiftS]; rw [e]; exact this

theorem blitS_lift_T {Γ : List VExpr} (ρ : Val) :
    ∀ i, BDefEq env (nat :: Γ) ((litS ρ).lift i) ((litS ρ).lift i) nat
  | 0 => .bvar .zero
  | i + 1 => (H.blitT (ρ i) (Γ := Γ)).weak henv

theorem bprecBodyT (h : PR) (ρ : Val) :
    BDefEq env [nat, nat] ((h.tr.liftN 1 2).subst (litS ρ).lift.lift)
      ((h.tr.liftN 1 2).subst (litS ρ).lift.lift) nat := by
  rw [liftN_subst_eq]
  refine h.btrT H henv fun i => ?_
  match i with
  | 0 => exact .bvar .zero
  | 1 => exact .bvar (.succ .zero)
  | i + 2 =>
    have := ((H.blitT (ρ (i + 1)) (Γ := [])).weak henv (B := nat)).weak henv (B := nat)
    have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [shiftS]; rw [e]; exact this

theorem bprecStepT (h : PR) (ρ : Val) :
    BDefEq env [] (.lam nat (.lam nat ((h.tr.liftN 1 2).subst (litS ρ).lift.lift)))
      (.lam nat (.lam nat ((h.tr.liftN 1 2).subst (litS ρ).lift.lift)))
      (.forallE nat (.forallE nat nat)) :=
  .lamDF H.bnatT (.lamDF H.bnatT (bprecBodyT H henv h ρ))

/-- **Adequacy** in the fragment. -/
theorem PR.badequate : ∀ (f : PR) (ρ : Val),
    BDefEq env [] (f.tr.subst (litS ρ)) (lit (f.eval ρ)) nat
  | .zero, _ => H.bzeroT
  | .var i, ρ => H.blitT _
  | .succ f, ρ => .appDF H.bsuccT (f.badequate ρ)
  | .push h g, ρ => by
    have hg := g.btrT H henv (blitS_lift_T H henv ρ (Γ := []))
    have h1 : BDefEq env [] ((PR.push h g).tr.subst (litS ρ))
        (.app (.lam nat (g.tr.subst (litS ρ).lift)) (lit (h.eval ρ))) nat :=
      .appDF (.lamDF H.bnatT hg) (h.badequate ρ)
    have h2 := BDefEq.beta hg (H.blitT (h.eval ρ) (Γ := []))
    rw [inst_lift_cons, litS_cons] at h2
    exact h1.trans (h2.trans (g.badequate _))
  | .prec g h, ρ => by
    have hz := g.btrT H henv (fun i => H.blitT (tl ρ i) (Γ := []))
    have hs := bprecStepT H henv h ρ
    let S := VExpr.lam nat (.lam nat ((h.tr.liftN 1 2).subst (litS ρ).lift.lift))
    suffices ∀ y, BDefEq env [] (natRec nat (g.tr.subst (litS (tl ρ))) S (lit y))
        (lit (recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)) nat by
      have := this (ρ 0)
      simpa [S, PR.tr, PR.eval, natRec, motive, subst_appN, lift_subst, litS_tail, VExpr.subst,
        litS] using this
    intro y
    induction y with
    | zero =>
      exact (H.biota_zero henv Inert.nat (fun _ => H.bnatT) hz hs).trans (g.badequate _)
    | succ y ih =>
      refine (H.biota_succ henv Inert.nat (fun _ => H.bnatT) hz hs (H.blitT y)).trans ?_
      have hb := precBody_inst h.tr ρ y
      have hbT : BDefEq env [nat] (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1)
          (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1) nat := by
        rw [hb]; exact h.btrT H henv (blitS_lift_T H henv _)
      have b1 : BDefEq env [] (.app S (lit y))
          (.lam nat (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1))
          (.forallE nat nat) :=
        BDefEq.beta (.lamDF H.bnatT (bprecBodyT H henv h ρ)) (H.blitT y)
      have b2 := BDefEq.beta hbT (H.blitT ((recNat (g.eval (tl ρ))
        (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)) (Γ := []))
      have e2 : (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1).inst
          (lit (recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)) =
          h.tr.subst (litS (vcons (recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)
            (vcons y (tl ρ)))) := by
        rw [hb, inst_lift_cons, litS_cons]
      rw [e2] at b2
      have c1 := BDefEq.appDF (BDefEq.app' hs (H.blitT y) rfl) ih
      have c2 := BDefEq.appDF b1 (H.blitT (recNat (g.eval (tl ρ))
        (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y) (Γ := []))
      exact c1.trans (c2.trans (b2.trans (h.badequate _)))

theorem bfnBodyT (f : PR) : BDefEq env [nat, nat] (fnBody f) (fnBody f) nat := by
  refine f.btrT H henv fun i => ?_
  match i with
  | 0 => exact .bvar .zero
  | 1 => exact .bvar (.succ .zero)
  | i + 2 => exact ((H.blitT 0 (Γ := [])).weak henv (B := nat)).weak henv (B := nat)

theorem bfnT (f : PR) : BDefEq env [] (fn f) (fn f) (.forallE nat (.forallE nat nat)) :=
  .lamDF H.bnatT (.lamDF H.bnatT (bfnBodyT H henv f))

theorem bfn_adequate (f : PR) (n k : Nat) :
    BDefEq env [] (.app (.app (fn f) (lit n)) (lit k)) (lit (f.eval (val2 k n))) nat := by
  have b1 : BDefEq env [] (.app (fn f) (lit n)) (.lam nat ((fnBody f).inst (lit n) 1))
      (.forallE nat nat) :=
    BDefEq.beta (.lamDF H.bnatT (bfnBodyT H henv f)) (H.blitT n)
  have hbT : BDefEq env [nat] ((fnBody f).inst (lit n) 1) ((fnBody f).inst (lit n) 1) nat := by
    rw [fnBody_inst]; exact f.btrT H henv (blitS_lift_T H henv _)
  have b2 := BDefEq.beta hbT (H.blitT k (Γ := []))
  have e2 : ((fnBody f).inst (lit n) 1).inst (lit k) = f.tr.subst (litS (val2 k n)) := by
    rw [fnBody_inst, inst_lift_cons, litS_cons]; rfl
  rw [e2] at b2
  exact (BDefEq.appDF b1 (H.blitT k)).trans (b2.trans (f.badequate H henv _))

end

section
variable {env : VEnv} {Γ : List VExpr}

theorem bprop_eq : BDefEq env Γ (.sort (.imax (.succ .zero) .zero)) (.sort .zero)
    (.sort (.succ (.imax (.succ .zero) .zero))) :=
  .sortDF ⟨trivial, trivial⟩ trivial (VLevel.equiv_def.2 fun _ => rfl) rfl

theorem bfalseT : BDefEq env Γ falseS falseS (.sort .zero) :=
  bprop_eq.defeq (BDefEq.forallE' .sort0 (.bvar .zero))

theorem btrueT : BDefEq env Γ trueS trueS (.sort .zero) := by
  have h1 : BDefEq env (.sort .zero :: Γ) (.bvar 0) (.bvar 0) (.sort .zero) := .bvar .zero
  have h2 : BDefEq env (.bvar 0 :: .sort .zero :: Γ) (.bvar 1) (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have h3 : BDefEq env (.sort .zero :: Γ) (.forallE (.bvar 0) (.bvar 1))
      (.forallE (.bvar 0) (.bvar 1)) (.sort .zero) :=
    .defeqDF (.sortDF (l := .imax .zero .zero) ⟨trivial, trivial⟩ trivial
      (VLevel.equiv_def.2 fun _ => rfl) rfl) (BDefEq.forallE' h1 h2)
  exact bprop_eq.defeq (BDefEq.forallE' .sort0 h3)

theorem btrueI_T : BDefEq env Γ trueI trueI trueS :=
  .lamDF .sort0 (.lamDF (.bvar .zero) (.bvar .zero))

end

section
variable {env : VEnv} (H : HasNat env)
include H

theorem bisZeroStepT {Γ : List VExpr} : BDefEq env Γ (.lam nat (.lam (.sort .zero) falseS))
    (.lam nat (.lam (.sort .zero) falseS)) (.forallE nat (.forallE (.sort .zero) (.sort .zero))) :=
  .lamDF H.bnatT (.lamDF .sort0 bfalseT)

theorem bisZero_congr {Γ : List VExpr} {n n' : VExpr} (hnT : BDefEq env Γ n n nat)
    (hn : BDefEq env Γ n n' nat) :
    BDefEq env Γ (isZero n) (isZero n') (.sort .zero) :=
  H.bnatRec_congr Inert.sort (fun _ => .sort0) btrueT (bisZeroStepT H) hnT hn

variable (henv : env.Ordered)
include henv

theorem bnotHaltsT (f : PR) (n : Nat) :
    BDefEq env [] (notHalts f n) (notHalts f n) (.sort (.imax (.succ .zero) (.imax .zero .zero))) := by
  have hf := bfnT H henv f
  have hfc : (fn f).ClosedN := hf.toIsDefEq.closedN henv trivial
  have hw := hf.weak henv (B := nat)
  rw [VExpr.lift, hfc.liftN_eq (Nat.zero_le _)] at hw
  exact BDefEq.forallE' H.bnatT (BDefEq.forallE'
    (H.bnatRecT Inert.sort (fun _ => .sort0) btrueT (bisZeroStepT H)
      (.app' (.app' hw (H.blitT n) rfl) (.bvar .zero) rfl))
    bfalseT)

/-- **Σ₁-completeness** in the fragment: a true halting sentence has a proof in `BDefEq`. -/
theorem bhalts_provable {f : PR} {n : Nat} (hf : f.Halts n) : BProvable env (halts f n) := by
  obtain ⟨k, hk⟩ := hf
  have hP := bnotHaltsT H henv f n
  have hc : (notHalts f n).ClosedN := hP.toIsDefEq.closedN henv trivial
  have h0 : BDefEq env [notHalts f n] (.bvar 0) (.bvar 0) (notHalts f n) := by
    have : BDefEq env [notHalts f n] (.bvar 0) (.bvar 0) (notHalts f n).lift := .bvar .zero
    rwa [show (notHalts f n).lift = notHalts f n from hc.liftN_eq (Nat.zero_le _)] at this
  have h1 : BDefEq env [notHalts f n] (.app (.bvar 0) (lit k)) (.app (.bvar 0) (lit k))
      (.forallE (isZero (.app (.app (fn f) (lit n)) (lit k))) falseS) := by
    refine .app' h0 (H.blitT k) ?_
    have hf : (fn f).ClosedN := (bfnT H henv f).toIsDefEq.closedN henv trivial
    show VExpr.forallE ((isZero _).inst (lit k)) (falseS.inst (lit k) 1) = _
    rw [isZero_inst]
    simp [VExpr.inst, hf.instN_eq (Nat.zero_le _), (Inert.lit n).inst]; rfl
  have hfnT : BDefEq env [] (.app (.app (fn f) (lit n)) (lit k))
      (.app (.app (fn f) (lit n)) (lit k)) nat :=
    .app' (.app' (bfnT H henv f) (H.blitT n) rfl) (H.blitT k) rfl
  have hconv : BDefEq env [] (isZero (.app (.app (fn f) (lit n)) (lit k))) trueS (.sort .zero) := by
    have := bisZero_congr H hfnT (bfn_adequate H henv f n k)
    rw [hk] at this
    exact this.trans (H.biota_zero henv Inert.sort (fun _ => .sort0) btrueT (bisZeroStepT H))
  have hc1 : (isZero (.app (.app (fn f) (lit n)) (lit k))).ClosedN :=
    hconv.toIsDefEq.closedN henv trivial
  have hconv' := hconv.weak henv (B := notHalts f n)
  rw [VExpr.lift, VExpr.lift, hc1.liftN_eq (Nat.zero_le _),
    show trueS.liftN 1 = trueS from rfl] at hconv'
  have h2 := BDefEq.appDF h1 (hconv'.symm.defeq btrueI_T)
  exact ⟨_, .lamDF hP h2⟩

end

/-- A proof of `halts f n` applied to one of `notHalts f n` proves `False`. -/
theorem brefute {env : VEnv} {f : PR} {n : Nat} :
    BProvable env (halts f n) → BProvable env (notHalts f n) → BProvable env falseS
  | ⟨_, hp⟩, ⟨_, hq⟩ => ⟨_, .app' hp hq rfl⟩

end Incomplete
