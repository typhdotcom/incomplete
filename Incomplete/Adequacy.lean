import Incomplete.Arith
import Incomplete.PR

/-!
# Primitive recursive codes in the object theory

`PR.tr f` is an object term of type `Nat` whose free variables are `f`'s. Substituting numerals
for them, it is definitionally equal to the numeral of `f`'s value: the object theory computes
every primitive recursive function on numerals by beta and iota.
-/

namespace Lean4Lean.Incomplete
open VExpr VEnv

namespace PR

def tr : PR → VExpr
  | zero => Incomplete.zero
  | var i => .bvar i
  | succ f => .app Incomplete.succ f.tr
  | push h g => .app (.lam nat g.tr) h.tr
  | prec g h => natRec nat g.tr.lift (.lam nat (.lam nat (h.tr.liftN 1 2))) (.bvar 0)

end PR

/-- Numerals for a valuation. -/
def litS (ρ : Val) : Subst := fun i => lit (ρ i)

/-- `τ` read past a lift. -/
def shiftS (τ : Subst) (n k : Nat) : Subst := fun i => τ (liftVar n i k)

theorem liftN_subst_eq (e : VExpr) :
    ∀ k (τ : Subst), (e.liftN n k).subst τ = e.subst (shiftS τ n k) := by
  induction e with
  | bvar i => intro k τ; rfl
  | sort | const => intro k τ; rfl
  | app f a ihf iha => intro k τ; simp [VExpr.liftN, VExpr.subst, ihf, iha]
  | proj _ _ e ih => intro k τ; simp [VExpr.liftN, VExpr.subst, ih]
  | lam A B ihA ihB | forallE A B ihA ihB =>
    intro k τ; simp only [VExpr.liftN, VExpr.subst, ihA, ihB]; congr 2
    funext i; cases i <;> simp [Subst.lift, shiftS]

theorem litS_cons (ρ : Val) (a : Nat) : (litS ρ).cons (lit a) = litS (vcons a ρ) := by
  funext i; cases i <;> rfl

theorem litS_tail (ρ : Val) : (litS ρ).tail = litS (tl ρ) := rfl

/-- The body of the step function of `prec g h`, instantiated at the predecessor `y`. -/
theorem precBody_inst (h : VExpr) (ρ : Val) (y : Nat) :
    ((h.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1 = h.subst (litS (vcons y (tl ρ))).lift := by
  rw [liftN_subst_eq, instN_eq, subst_subst]; congr 1; funext i
  rcases i with _ | _ | i
  · simp [Subst.comp, shiftS, Subst.lift, Subst.liftN, liftVar]
  · simp [Subst.comp, Subst.lift, Subst.liftN, Subst.tail, Subst.cons, litS, liftVar, shiftS,
      VExpr.lift, (Inert.lit _).liftN]
  · have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [Subst.comp, shiftS]; rw [e]
    simp [Subst.lift, litS, VExpr.lift, (Inert.lit _).liftN, (Inert.lit _).subst]

/-- The closed function `fun n k => f` of a code, variables past the first two read as `0`. -/
def fnBody (f : PR) : VExpr := f.tr.subst (litS fun _ => 0).lift.lift
def fn (f : PR) : VExpr := .lam nat (.lam nat (fnBody f))

theorem fnBody_inst (f : PR) (n : Nat) :
    (fnBody f).inst (lit n) 1 = f.tr.subst (litS (vcons n fun _ => 0)).lift := by
  rw [fnBody, instN_eq, subst_subst]; congr 1; funext i
  rcases i with _ | _ | i
  · rfl
  · simp [Subst.comp, Subst.lift, Subst.liftN, Subst.tail, Subst.cons, litS, VExpr.lift,
      (Inert.lit _).liftN]
  · simp [Subst.comp, Subst.lift, litS, VExpr.lift, (Inert.lit _).liftN, (Inert.lit _).subst]

section
variable {env : VEnv} (H : HasNat env) (henv : env.Ordered)
include H henv

theorem PR.trT : ∀ (f : PR) {Γ : List VExpr} {σ : Subst}, (∀ i, env.HasType 0 Γ (σ i) nat) →
    env.HasType 0 Γ (f.tr.subst σ) nat
  | .zero, _, _, _ => H.zeroT
  | .var i, _, _, hσ => hσ i
  | .succ f, _, _, hσ => .app' H.succT (f.trT hσ) rfl
  | .push h g, Γ, σ, hσ => by
    refine .app' (.lam H.natT (g.trT ?_)) (h.trT hσ) rfl
    intro i; cases i with
    | zero => exact .bvar .zero
    | succ i => exact (hσ i).weak henv
  | .prec g h, Γ, σ, hσ => by
    refine H.natRecT Inert.nat (fun _ => H.natT) ?_ ?_ (hσ 0)
    · rw [lift_subst]; exact g.trT fun i => hσ (i + 1)
    · refine .lam H.natT (.lam H.natT ?_)
      rw [liftN_subst_eq]
      refine h.trT fun i => ?_
      match i with
      | 0 => exact .bvar .zero
      | 1 => exact .bvar (.succ .zero)
      | i + 2 =>
        have := ((hσ (i + 1)).weak henv (B := nat)).weak henv (B := nat)
        have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
        simp only [shiftS]; rw [e]; exact this

omit henv in
theorem litS_T (ρ : Val) : ∀ i, env.HasType 0 Γ (litS ρ i) nat := fun _ => H.litT _

theorem litS_lift_T (ρ : Val) : ∀ i, env.HasType 0 (nat :: Γ) ((litS ρ).lift i) nat
  | 0 => .bvar .zero
  | i + 1 => (H.litT (ρ i) (Γ := Γ)).weak henv

theorem precBodyT (h : PR) (ρ : Val) :
    env.HasType 0 [nat, nat] ((h.tr.liftN 1 2).subst (litS ρ).lift.lift) nat := by
  rw [liftN_subst_eq]
  refine h.trT H henv fun i => ?_
  match i with
  | 0 => exact .bvar .zero
  | 1 => exact .bvar (.succ .zero)
  | i + 2 =>
    have := ((H.litT (ρ (i + 1)) (Γ := []) (U := 0)).weak henv (B := nat)).weak henv
      (B := nat)
    have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
    simp only [shiftS]; rw [e]; exact this

theorem precStepT (h : PR) (ρ : Val) :
    env.HasType 0 [] (.lam nat (.lam nat ((h.tr.liftN 1 2).subst (litS ρ).lift.lift)))
      (.forallE nat (.forallE nat nat)) :=
  .lam H.natT (.lam H.natT (precBodyT H henv h ρ))

/-- **Adequacy.** The object theory computes primitive recursive functions on numerals. -/
theorem PR.adequate : ∀ (f : PR) (ρ : Val),
    env.IsDefEq 0 [] (f.tr.subst (litS ρ)) (lit (f.eval ρ)) nat
  | .zero, _ => H.zeroT
  | .var i, ρ => H.litT _
  | .succ f, ρ => .appDF H.succT (f.adequate ρ)
  | .push h g, ρ => by
    have hg := g.trT H henv (litS_lift_T H henv ρ (Γ := []))
    have h1 : env.IsDefEq 0 [] ((PR.push h g).tr.subst (litS ρ))
        (.app (.lam nat (g.tr.subst (litS ρ).lift)) (lit (h.eval ρ))) nat :=
      .appDF (HasType.lam H.natT hg) (h.adequate ρ)
    have h2 := IsDefEq.beta hg (H.litT (h.eval ρ) (Γ := []))
    rw [inst_lift_cons, litS_cons] at h2
    exact h1.trans (h2.trans (g.adequate _))
  | .prec g h, ρ => by
    have hz := g.trT H henv (litS_T H (tl ρ) (Γ := []))
    have hs := precStepT H henv h ρ
    let S := VExpr.lam nat (.lam nat ((h.tr.liftN 1 2).subst (litS ρ).lift.lift))
    suffices ∀ y, env.IsDefEq 0 [] (natRec nat (g.tr.subst (litS (tl ρ))) S (lit y))
        (lit (recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)) nat by
      have := this (ρ 0)
      simpa [S, PR.tr, PR.eval, natRec, motive, subst_appN, lift_subst, litS_tail, VExpr.subst,
        litS] using this
    intro y
    induction y with
    | zero =>
      exact (H.iota_zero henv Inert.nat (fun _ => H.natT) hz hs).trans (g.adequate _)
    | succ y ih =>
      refine (H.iota_succ henv Inert.nat (fun _ => H.natT) hz hs (H.litT y)).trans ?_
      have hb := precBody_inst h.tr ρ y
      have hbT : env.HasType 0 [nat] (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1)
          nat := by
        rw [hb]; exact h.trT H henv (litS_lift_T H henv _)
      have b1 : env.IsDefEq 0 [] (.app S (lit y))
          (.lam nat (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1))
          (.forallE nat nat) :=
        IsDefEq.beta (HasType.lam H.natT (precBodyT H henv h ρ)) (H.litT y)
      have b2 := IsDefEq.beta hbT (H.litT ((recNat (g.eval (tl ρ))
        (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)) (Γ := []))
      have e2 : (((h.tr.liftN 1 2).subst (litS ρ).lift.lift).inst (lit y) 1).inst
          (lit (recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)) =
          h.tr.subst (litS (vcons (recNat (g.eval (tl ρ)) (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y)
            (vcons y (tl ρ)))) := by
        rw [hb, inst_lift_cons, litS_cons]
      rw [e2] at b2
      have c1 := IsDefEq.appDF (HasType.app' hs (H.litT y) rfl) ih
      have c2 := IsDefEq.appDF b1 (H.litT (recNat (g.eval (tl ρ))
        (fun y r => h.eval (vcons r (vcons y (tl ρ)))) y) (Γ := []))
      exact c1.trans (c2.trans (b2.trans (h.adequate _)))

theorem fnBodyT (f : PR) : env.HasType 0 [nat, nat] (fnBody f) nat := by
  refine f.trT H henv fun i => ?_
  match i with
  | 0 => exact .bvar .zero
  | 1 => exact .bvar (.succ .zero)
  | i + 2 => exact ((H.litT 0 (Γ := []) (U := 0)).weak henv (B := nat)).weak henv (B := nat)

theorem fnT (f : PR) : env.HasType 0 [] (fn f) (.forallE nat (.forallE nat nat)) :=
  .lam H.natT (.lam H.natT (fnBodyT H henv f))

/-- `fn f n k` computes `f [k, n]`. -/
theorem fn_adequate (f : PR) (n k : Nat) :
    env.IsDefEq 0 [] (.app (.app (fn f) (lit n)) (lit k)) (lit (f.eval (val2 k n))) nat := by
  have b1 : env.IsDefEq 0 [] (.app (fn f) (lit n)) (.lam nat ((fnBody f).inst (lit n) 1))
      (.forallE nat nat) :=
    IsDefEq.beta (HasType.lam H.natT (fnBodyT H henv f)) (H.litT n)
  have hbT : env.HasType 0 [nat] ((fnBody f).inst (lit n) 1) nat := by
    rw [fnBody_inst]; exact f.trT H henv (litS_lift_T H henv _)
  have b2 := IsDefEq.beta hbT (H.litT k (Γ := []))
  have e2 : ((fnBody f).inst (lit n) 1).inst (lit k) = f.tr.subst (litS (val2 k n)) := by
    rw [fnBody_inst, inst_lift_cons, litS_cons]; rfl
  rw [e2] at b2
  exact (IsDefEq.appDF b1 (H.litT k)).trans (b2.trans (f.adequate H henv _))

end

end Lean4Lean.Incomplete
