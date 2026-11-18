import Incomplete.Induct
import Incomplete.Adequacy

/-!
# The judgment of the object-level development

The object-level development runs over a judgment `env : Typing`, an environment with a relation
`env.IsDefEq Γ e₁ e₂ A`, through the rules of `ObjEnv env`: the typing rules restricted to sorts
`Prop` and `Type`, weakening and instantiation, the iota rules of `Nat.rec` at a constant motive
in `Type`, and adequacy of `PR.tr`. Full typing `full env` (`env.IsDefEq 0`) has them for every
ordered `env` with `Nat` (`ObjEnv.full`). The derived rules below are proved from these alone.
-/

namespace Incomplete
open Lean4Lean
open VExpr

/-- An environment with a definitional-equality judgment over it. -/
structure Typing where
  env : VEnv
  IsDefEq : List VExpr → VExpr → VExpr → VExpr → Prop

namespace Typing

/-- `e : A` in context `Γ`. -/
def HasType (env : Typing) (Γ : List VExpr) (e A : VExpr) : Prop := env.IsDefEq Γ e e A

end Typing

/-- Full typing in `env`, at no universe parameters. -/
def full (env : VEnv) : Typing := ⟨env, env.IsDefEq 0⟩

instance : Coe VEnv Typing := ⟨full⟩

/-- A judgment closed under the rules the object-level development uses. -/
class Obj.ObjEnv (env : Typing) : Prop where
  hasNat : HasNat env.env
  ordered : env.env.Ordered
  toFull : env.IsDefEq Γ e₁ e₂ A → env.env.IsDefEq 0 Γ e₁ e₂ A
  bvar : Lookup Γ i A → env.HasType Γ (.bvar i) A
  symm : env.IsDefEq Γ e e' A → env.IsDefEq Γ e' e A
  trans : env.IsDefEq Γ e₁ e₂ A → env.IsDefEq Γ e₂ e₃ A → env.IsDefEq Γ e₁ e₃ A
  sortDF : l.WF 0 → l'.WF 0 → l ≈ l' → l.eval [] = 0 →
    env.IsDefEq Γ (.sort l) (.sort l') (.sort (.succ l))
  constDF : env.env.constants c = some ci → (∀ l ∈ ls, l.WF 0) → (∀ l ∈ ls', l.WF 0) →
    ls.length = ci.uvars → List.Forall₂ (· ≈ ·) ls ls' → (∀ l ∈ ls, l.eval [] ≤ 1) →
    env.IsDefEq Γ (.const c ls) (.const c ls') (ci.type.instL ls)
  appDF : env.IsDefEq Γ f f' (.forallE A B) → env.IsDefEq Γ a a' A →
    env.IsDefEq Γ (.app f a) (.app f' a') (B.inst a)
  lamDF : env.IsDefEq Γ A A' (.sort u) → env.IsDefEq (A::Γ) body body' B →
    env.IsDefEq Γ (.lam A body) (.lam A' body') (.forallE A B)
  forallEDF : env.IsDefEq Γ A A' (.sort u) → env.IsDefEq (A::Γ) body body' (.sort v) →
    u.WF 0 → v.WF 0 → u.eval [] ≤ 1 → v.eval [] ≤ 1 →
    env.IsDefEq Γ (.forallE A body) (.forallE A' body') (.sort (.imax u v))
  defeqDF : env.IsDefEq Γ A B (.sort u) → env.IsDefEq Γ e₁ e₂ A → env.IsDefEq Γ e₁ e₂ B
  beta : env.HasType (A::Γ) e B → env.HasType Γ e' A →
    env.IsDefEq Γ (.app (.lam A e) e') (e.inst e') (B.inst e')
  eta : env.HasType Γ e (.forallE A B) →
    env.IsDefEq Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B)
  proofIrrel : env.HasType Γ p (.sort .zero) → env.HasType Γ h p → env.HasType Γ h' p →
    env.IsDefEq Γ h h' p
  weakN : Ctx.LiftN n k Γ Γ' → env.IsDefEq Γ e₁ e₂ A →
    env.IsDefEq Γ' (e₁.liftN n k) (e₂.liftN n k) (A.liftN n k)
  instN : env.HasType Γ₀ e₀ A₀ → Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ → env.IsDefEq Γ₁ e₁ e₂ A →
    env.IsDefEq Γ (e₁.inst e₀ k) (e₂.inst e₀ k) (A.inst e₀ k)
  natRec_zero : A.ClosedN → (∀ Γ, env.HasType Γ A (.sort (.succ .zero))) → env.HasType Γ z A →
    env.HasType Γ s (.forallE nat (.forallE A A)) → env.IsDefEq Γ (natRec A z s zero) z A
  natRec_succ : A.ClosedN → (∀ Γ, env.HasType Γ A (.sort (.succ .zero))) → env.HasType Γ z A →
    env.HasType Γ s (.forallE nat (.forallE A A)) → env.HasType Γ n nat →
    env.IsDefEq Γ (natRec A z s (.app succ n)) (.app (.app s n) (natRec A z s n)) A
  adequate : ∀ (f : PR) (ρ : Val), env.IsDefEq [] (f.tr.subst (litS ρ)) (lit (f.eval ρ)) nat

namespace Typing
open Obj

variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

/-! ### The rules, by name -/

theorem IsDefEq.symm (h : env.IsDefEq Γ e e' A) : env.IsDefEq Γ e' e A := E.symm h
theorem IsDefEq.trans (h₁ : env.IsDefEq Γ e₁ e₂ A) (h₂ : env.IsDefEq Γ e₂ e₃ A) :
    env.IsDefEq Γ e₁ e₃ A := E.trans h₁ h₂
theorem IsDefEq.appDF (h₁ : env.IsDefEq Γ f f' (.forallE A B)) (h₂ : env.IsDefEq Γ a a' A) :
    env.IsDefEq Γ (.app f a) (.app f' a') (B.inst a) := E.appDF h₁ h₂
theorem IsDefEq.lamDF (h₁ : env.IsDefEq Γ A A' (.sort u)) (h₂ : env.IsDefEq (A::Γ) b b' B) :
    env.IsDefEq Γ (.lam A b) (.lam A' b') (.forallE A B) := E.lamDF h₁ h₂
theorem IsDefEq.forallEDF (h₁ : env.IsDefEq Γ A A' (.sort u))
    (h₂ : env.IsDefEq (A::Γ) b b' (.sort v)) (hu' : u.WF 0 := by decide)
    (hv' : v.WF 0 := by decide) (hu : u.eval [] ≤ 1 := by decide)
    (hv : v.eval [] ≤ 1 := by decide) :
    env.IsDefEq Γ (.forallE A b) (.forallE A' b') (.sort (.imax u v)) :=
  E.forallEDF h₁ h₂ hu' hv' hu hv
theorem IsDefEq.defeqDF (h₁ : env.IsDefEq Γ A B (.sort u)) (h₂ : env.IsDefEq Γ e₁ e₂ A) :
    env.IsDefEq Γ e₁ e₂ B := E.defeqDF h₁ h₂
theorem IsDefEq.beta (h₁ : env.HasType (A::Γ) e B) (h₂ : env.HasType Γ e' A) :
    env.IsDefEq Γ (.app (.lam A e) e') (e.inst e') (B.inst e') := E.beta h₁ h₂
theorem IsDefEq.eta (h : env.HasType Γ e (.forallE A B)) :
    env.IsDefEq Γ (.lam A (.app e.lift (.bvar 0))) e (.forallE A B) := E.eta h
theorem IsDefEq.proofIrrel (h₁ : env.HasType Γ p (.sort .zero)) (h₂ : env.HasType Γ h p)
    (h₃ : env.HasType Γ h' p) : env.IsDefEq Γ h h' p := E.proofIrrel h₁ h₂ h₃
theorem IsDefEq.sortDF (h₁ : l.WF 0) (h₂ : l'.WF 0) (h₃ : l ≈ l') (h₄ : l.eval [] = 0) :
    env.IsDefEq Γ (.sort l) (.sort l') (.sort (.succ l)) := E.sortDF h₁ h₂ h₃ h₄
theorem IsDefEq.toFull (h : env.IsDefEq Γ e₁ e₂ A) : env.env.IsDefEq 0 Γ e₁ e₂ A := E.toFull h

theorem IsDefEq.hasType (h : env.IsDefEq Γ e₁ e₂ A) : env.HasType Γ e₁ A ∧ env.HasType Γ e₂ A :=
  ⟨h.trans h.symm, h.symm.trans h⟩
theorem IsDefEq.defeq (h₁ : env.IsDefEq Γ A B (.sort u)) (h₂ : env.HasType Γ e A) :
    env.HasType Γ e B := h₁.defeqDF h₂
theorem IsDefEq.defeq' (h₁ : env.IsDefEq Γ A B (.sort u)) (h₂ : env.HasType Γ e B) :
    env.HasType Γ e A := h₁.symm.defeqDF h₂

theorem IsDefEq.weakN (W : Ctx.LiftN n k Γ Γ') (h : env.IsDefEq Γ e₁ e₂ A) :
    env.IsDefEq Γ' (e₁.liftN n k) (e₂.liftN n k) (A.liftN n k) := E.weakN W h
theorem IsDefEq.weak (h : env.IsDefEq Γ e₁ e₂ A) : env.IsDefEq (B::Γ) e₁.lift e₂.lift A.lift :=
  h.weakN .one
theorem IsDefEq.instN (h₀ : env.HasType Γ₀ e₀ A₀) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h : env.IsDefEq Γ₁ e₁ e₂ A) : env.IsDefEq Γ (e₁.inst e₀ k) (e₂.inst e₀ k) (A.inst e₀ k) :=
  E.instN h₀ W h

theorem IsDefEq.closedN (h : env.IsDefEq [] e₁ e₂ A) : e₁.ClosedN ∧ e₂.ClosedN ∧ A.ClosedN :=
  h.toFull.closedN' E.ordered.closed ⟨⟩

/-- A closed judgment holds in every context. -/
theorem IsDefEq.weak0 (h : env.IsDefEq [] e₁ e₂ A) : env.IsDefEq Γ e₁ e₂ A := by
  have ⟨c1, c2, c3⟩ := h.closedN
  have W : Ctx.LiftN Γ.length 0 [] Γ := by simpa using Ctx.LiftN.zero (Γ := []) Γ
  have := h.weakN W
  rwa [c1.liftN_eq (Nat.zero_le _), c2.liftN_eq (Nat.zero_le _),
    c3.liftN_eq (Nat.zero_le _)] at this

theorem forall₂_rfl' : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls
  | [] => .nil
  | _ :: ls => .cons rfl (forall₂_rfl' ls)

theorem HasType.bvar (h : Lookup Γ i A) : env.HasType Γ (.bvar i) A := E.bvar h
theorem HasType.sort0 : env.HasType Γ (.sort .zero) (.sort (.succ .zero)) :=
  E.sortDF trivial trivial rfl rfl
theorem HasType.const' (h₁ : env.env.constants c = some ci) (h₂ : ∀ l ∈ ls, l.WF 0)
    (h₃ : ls.length = ci.uvars) (h₄ : ∀ l ∈ ls, l.eval [] ≤ 1) (eq : ci.type.instL ls = ty') :
    env.HasType Γ (.const c ls) ty' :=
  eq ▸ E.constDF h₁ h₂ h₂ h₃ (forall₂_rfl' ls) h₄
theorem HasType.app (h₁ : env.HasType Γ f (.forallE A B)) (h₂ : env.HasType Γ a A) :
    env.HasType Γ (.app f a) (B.inst a) := E.appDF h₁ h₂
theorem HasType.app' (h₁ : env.HasType Γ f (.forallE A B)) (h₂ : env.HasType Γ a A)
    (eq : B.inst a = B') : env.HasType Γ (.app f a) B' := eq ▸ E.appDF h₁ h₂
theorem HasType.lam (h₁ : env.HasType Γ A (.sort u)) (h₂ : env.HasType (A::Γ) b B) :
    env.HasType Γ (.lam A b) (.forallE A B) := E.lamDF h₁ h₂
theorem HasType.forallE (h₁ : env.HasType Γ A (.sort u)) (h₂ : env.HasType (A::Γ) b (.sort v))
    (hu' : u.WF 0 := by decide) (hv' : v.WF 0 := by decide)
    (hu : u.eval [] ≤ 1 := by decide) (hv : v.eval [] ≤ 1 := by decide) :
    env.HasType Γ (.forallE A b) (.sort (.imax u v)) := E.forallEDF h₁ h₂ hu' hv' hu hv

theorem HasType.weakN (W : Ctx.LiftN n k Γ Γ') (h : env.HasType Γ e A) :
    env.HasType Γ' (e.liftN n k) (A.liftN n k) := E.weakN W h
theorem HasType.weak (h : env.HasType Γ e A) : env.HasType (B::Γ) e.lift A.lift := h.weakN .one
theorem HasType.weak0 (h : env.HasType [] e A) : env.HasType Γ e A := IsDefEq.weak0 h
theorem HasType.instN (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) (h : env.HasType Γ₁ e A)
    (h₀ : env.HasType Γ₀ e₀ A₀) : env.HasType Γ (e.inst e₀ k) (A.inst e₀ k) := E.instN h₀ W h
theorem HasType.closedN (h : env.HasType [] e A) : e.ClosedN ∧ A.ClosedN :=
  ⟨h.toFull.closedN E.ordered trivial, (IsDefEq.closedN h).2.2⟩

end Typing

/-! ### Derived rules -/

namespace Obj
open Typing

variable {env : Typing} [E : ObjEnv env] {Γ : List VExpr}

/-- `∀ x : A, B` with `B` a proposition is a proposition. -/
theorem forallE_prop (hA : env.HasType Γ A (.sort u)) (hB : env.HasType (A :: Γ) B (.sort .zero))
    (hu' : u.WF 0 := by decide) (hu : u.eval [] ≤ 1 := by decide) :
    env.HasType Γ (.forallE A B) (.sort .zero) :=
  (IsDefEq.sortDF (l := .imax u .zero) (l' := .zero) ⟨hu', trivial⟩ trivial
    (VLevel.equiv_def.2 fun _ => by simp [VLevel.eval, Lean.Nat.imax])
    (by simp [VLevel.eval, Lean.Nat.imax])).defeq
    (HasType.forallE (v := .zero) hA hB hu' (by decide) hu (by decide))

theorem natT : env.HasType Γ nat (.sort (.succ .zero)) :=
  .const' E.hasNat.hNat (by simp) rfl (by simp) rfl
theorem zeroT : env.HasType Γ zero nat := .const' E.hasNat.hZero (by simp) rfl (by simp) rfl
theorem succT : env.HasType Γ succ (.forallE nat nat) :=
  .const' E.hasNat.hSucc (by simp) rfl (by simp) rfl
theorem litNatT : ∀ n, env.HasType Γ (lit n) nat
  | 0 => zeroT
  | n + 1 => .app' succT (litNatT n) rfl

theorem falseT : env.HasType Γ falseS (.sort .zero) := forallE_prop .sort0 (.bvar .zero)

theorem trueT : env.HasType Γ trueS (.sort .zero) :=
  forallE_prop .sort0 (forallE_prop (.bvar .zero) (.bvar (.succ .zero)))

theorem trueI_T : env.HasType Γ trueI trueS := .lam .sort0 (.lam (.bvar .zero) (.bvar .zero))

theorem isZeroStepT : env.HasType Γ (.lam nat (.lam (.sort .zero) falseS))
    (.forallE nat (.forallE (.sort .zero) (.sort .zero))) :=
  .lam natT (.lam .sort0 falseT)

theorem motive_app {A n : VExpr} (hI : Inert A)
    (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero))) (hn : env.HasType Γ n nat) :
    env.IsDefEq Γ (.app (motive A) n) A (.sort (.succ .zero)) := by
  have := IsDefEq.beta (hA (nat :: Γ)) hn
  rwa [hI.inst] at this

theorem succMinor_conv {A : VExpr} (hI : Inert A) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero))) :
    env.IsDefEq Γ (.forallE nat (.forallE A A))
      (.forallE nat (.forallE (.app (motive A) (.bvar 0)) (.app (motive A) (.app succ (.bvar 1)))))
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallEDF natT (.forallEDF (motive_app hI hA (.bvar .zero)).symm
    (motive_app hI hA (.app' succT (.bvar (.succ .zero)) rfl)).symm)

theorem natRecHeadDF {A z z' s s' : VExpr} (hI : Inert A)
    (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.IsDefEq Γ z z' A) (hs : env.IsDefEq Γ s s' (.forallE nat (.forallE A A))) :
    env.IsDefEq Γ (.appN (.const ``Nat.rec [.succ .zero]) [motive A, z, s])
      (.appN (.const ``Nat.rec [.succ .zero]) [motive A, z', s'])
      (.forallE nat (.app (motive A) (.bvar 0))) := by
  have hM : env.HasType Γ (motive A) (.forallE nat (.sort (.succ .zero))) := .lam natT (hA _)
  have h0 : env.HasType Γ (.const ``Nat.rec [.succ .zero]) (recTy.instL [.succ .zero]) :=
    .const' E.hasNat.hRec (by simp [VLevel.WF]) rfl (by simp [VLevel.eval]) rfl
  have h1 := HasType.app h0 hM
  have e1 : (VExpr.instL [.succ .zero] (.forallE Incomplete.zeroTy (.forallE succTy
      (.forallE nat (.app (.bvar 3) (.bvar 0)))))).inst (motive A) =
      .forallE (.app (motive A) zero) (.forallE
        (.forallE nat (.forallE (.app (motive A) (.bvar 0))
          (.app (motive A) (.app succ (.bvar 1)))))
        (.forallE nat (.app (motive A) (.bvar 0)))) := by
    simp [Incomplete.zeroTy, succTy, VExpr.instL, VExpr.inst, instVar, (Inert.motive hI).liftN]
  rw [e1] at h1
  have h2 := IsDefEq.appDF h1 ((motive_app hI hA zeroT).symm.defeqDF hz)
  simp only [VExpr.inst, (Inert.motive hI).inst] at h2
  have h3 := IsDefEq.appDF h2 ((succMinor_conv hI hA).defeqDF hs)
  simp only [VExpr.inst, (Inert.motive hI).inst] at h3
  exact h3

theorem natRecDF {A z z' s s' n n' : VExpr} (hI : Inert A)
    (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.IsDefEq Γ z z' A) (hs : env.IsDefEq Γ s s' (.forallE nat (.forallE A A)))
    (hn : env.IsDefEq Γ n n' nat) :
    env.IsDefEq Γ (natRec A z s n) (natRec A z' s' n') A := by
  have h4 := IsDefEq.appDF (natRecHeadDF hI hA hz hs) hn
  simp [VExpr.inst, instVar, (Inert.motive hI).inst] at h4
  exact .defeqDF (motive_app hI hA hn.hasType.1) h4

theorem natRecT {A z s n : VExpr} (hI : Inert A) (hA : ∀ Γ, env.HasType Γ A (.sort (.succ .zero)))
    (hz : env.HasType Γ z A) (hs : env.HasType Γ s (.forallE nat (.forallE A A)))
    (hn : env.HasType Γ n nat) : env.HasType Γ (natRec A z s n) A :=
  natRecDF hI hA hz hs hn

theorem trSubstT : ∀ (f : PR) {Γ : List VExpr} {σ : Subst}, (∀ i, env.HasType Γ (σ i) nat) →
    env.HasType Γ (f.tr.subst σ) nat
  | .zero, _, _, _ => zeroT
  | .var i, _, _, hσ => hσ i
  | .succ f, _, _, hσ => .app' succT (trSubstT f hσ) rfl
  | .push h g, Γ, σ, hσ => by
    refine .app' (.lam natT (trSubstT g ?_)) (trSubstT h hσ) rfl
    intro i; cases i with
    | zero => exact .bvar .zero
    | succ i => exact (hσ i).weak
  | .prec g h, Γ, σ, hσ => by
    refine natRecT Inert.nat (fun _ => natT) ?_ ?_ (hσ 0)
    · rw [lift_subst]; exact trSubstT g fun i => hσ (i + 1)
    · refine .lam natT (.lam natT ?_)
      rw [liftN_subst_eq]
      refine trSubstT h fun i => ?_
      match i with
      | 0 => exact .bvar .zero
      | 1 => exact .bvar (.succ .zero)
      | i + 2 =>
        have := ((hσ (i + 1)).weak (B := nat)).weak (B := nat)
        have e : liftVar 1 (i + 2) 2 = i + 1 + 2 := by rw [liftVar_le (by omega)]; omega
        simp only [shiftS]; rw [e]; exact this

theorem fnT (f : PR) : env.HasType [] (fn f) (.forallE nat (.forallE nat nat)) := by
  refine .lam natT (.lam natT (trSubstT f fun i => ?_))
  match i with
  | 0 => exact .bvar .zero
  | 1 => exact .bvar (.succ .zero)
  | i + 2 => exact ((litNatT 0 (Γ := [])).weak (B := nat)).weak (B := nat)

theorem isZeroT {n : VExpr} (hn : env.HasType Γ n nat) : env.HasType Γ (isZero n) (.sort .zero) :=
  natRecT Inert.sort (fun _ => .sort0) trueT isZeroStepT hn

end Obj

/-! ### Full typing -/

namespace Obj
open VEnv

/-- The step type `Nat → A → A`. -/
abbrev stepT (A : VExpr) : VExpr := .forallE nat (.forallE A A)

theorem stepT_inert {A : VExpr} (hI : Inert A) : Inert (stepT A) :=
  ⟨fun _ _ => by simp [VExpr.liftN, hI.liftN], fun _ _ => by simp [VExpr.inst, hI.inst],
   fun _ => by simp [VExpr.subst, hI.subst]⟩

section
variable {env : VEnv} (H : HasNat env) (henv : env.Ordered) {Γ : List VExpr} {A z s n : VExpr}
include H henv

omit henv in
theorem full_stepT_T (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero))) :
    env.HasType 0 Γ (stepT A) (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallE H.natT (.forallE (hA _) (hA _))

theorem full_natRec_zero (hc : A.ClosedN) (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 Γ z A) (hs : env.HasType 0 Γ s (stepT A)) :
    env.IsDefEq 0 Γ (natRec A z s zero) z A := by
  have hI := Inert.ofClosed hc
  have hΔ : OnCtx [stepT A, A] (env.IsType 0) :=
    ⟨⟨trivial, _, hA _⟩, _, full_stepT_T H hA⟩
  have hz0 : env.HasType 0 [stepT A, A] (.bvar 1) A := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.succ (A := stepT A) (Lookup.zero (Γ := [])
      (ty := A))); simpa only [hI.liftN] using this
  have hs0 : env.HasType 0 [stepT A, A] (.bvar 0) (stepT A) := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.zero (Γ := [A]) (ty := stepT A))
    simpa only [(stepT_inert hI).liftN] using this
  have h := H.iota_zero' henv hΔ hI hA hz0 hs0
  have hcl : CtxClosed [stepT A, A] :=
    ⟨⟨trivial, hc⟩, ⟨trivial, hc.mono (Nat.zero_le _), hc.mono (Nat.zero_le _)⟩⟩
  have h := h.weakR henv hcl Γ
  have hs' : env.HasType 0 (A :: Γ) s.lift (stepT A) := by
    have : env.HasType 0 (A :: Γ) s.lift (stepT A).lift := IsDefEq.weak henv hs
    simpa only [(stepT_inert hI).liftN] using this
  have h := h.instN henv hs' .zero
  have h := h.instN henv hz .zero
  simpa [natRec, motive, VExpr.inst, hI.inst, inst_lift] using h

theorem full_natRec_succ (hc : A.ClosedN) (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 Γ z A) (hs : env.HasType 0 Γ s (stepT A)) (hn : env.HasType 0 Γ n nat) :
    env.IsDefEq 0 Γ (natRec A z s (.app succ n)) (.app (.app s n) (natRec A z s n)) A := by
  have hI := Inert.ofClosed hc
  have hΔ : OnCtx [nat, stepT A, A] (env.IsType 0) :=
    ⟨⟨⟨trivial, _, hA _⟩, _, full_stepT_T H hA⟩, _, H.natT⟩
  have hz0 : env.HasType 0 [nat, stepT A, A] (.bvar 2) A := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.succ (A := nat) (Lookup.succ (A := stepT A)
      (Lookup.zero (Γ := []) (ty := A)))); simpa only [hI.liftN] using this
  have hs0 : env.HasType 0 [nat, stepT A, A] (.bvar 1) (stepT A) := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.succ (A := nat)
      (Lookup.zero (Γ := [A]) (ty := stepT A)))
    simpa only [(stepT_inert hI).liftN] using this
  have h := H.iota_succ' henv hΔ hI hA hz0 hs0 (.bvar .zero)
  have hcl : CtxClosed [nat, stepT A, A] :=
    ⟨⟨⟨trivial, hc⟩, ⟨trivial, hc.mono (Nat.zero_le _), hc.mono (Nat.zero_le _)⟩⟩,
      trivial⟩
  have h := h.weakR henv hcl Γ
  have hn' : env.HasType 0 (stepT A :: A :: Γ) n.lift.lift nat :=
    IsDefEq.weak henv (IsDefEq.weak henv hn)
  have hs' : env.HasType 0 (A :: Γ) s.lift (stepT A) := by
    have : env.HasType 0 (A :: Γ) s.lift (stepT A).lift := IsDefEq.weak henv hs
    simpa only [(stepT_inert hI).liftN] using this
  have h := h.instN henv hn' .zero
  have h := h.instN henv hs' .zero
  have h := h.instN henv hz .zero
  simpa [natRec, motive, VExpr.inst, hI.inst, inst_lift] using h

/-- Full typing has the rules of the object-level development. -/
theorem ObjEnv.full : ObjEnv (full env) where
  hasNat := H
  ordered := henv
  toFull h := h
  bvar h := VEnv.IsDefEq.bvar h
  symm h := VEnv.IsDefEq.symm h
  trans h₁ h₂ := VEnv.IsDefEq.trans h₁ h₂
  sortDF h₁ h₂ h₃ _ := VEnv.IsDefEq.sortDF h₁ h₂ h₃
  constDF h₁ h₂ h₃ h₄ h₅ _ := VEnv.IsDefEq.constDF h₁ h₂ h₃ h₄ h₅
  appDF h₁ h₂ := VEnv.IsDefEq.appDF h₁ h₂
  lamDF h₁ h₂ := VEnv.IsDefEq.lamDF h₁ h₂
  forallEDF h₁ h₂ _ _ _ _ := VEnv.IsDefEq.forallEDF h₁ h₂
  defeqDF h₁ h₂ := VEnv.IsDefEq.defeqDF h₁ h₂
  beta h₁ h₂ := VEnv.IsDefEq.beta h₁ h₂
  eta h := VEnv.IsDefEq.eta h
  proofIrrel h₁ h₂ h₃ := VEnv.IsDefEq.proofIrrel h₁ h₂ h₃
  weakN W h := VEnv.IsDefEq.weakN henv W h
  instN h₀ W h := VEnv.IsDefEq.instN henv h₀ W h
  natRec_zero hc hA hz hs := full_natRec_zero H henv hc hA hz hs
  natRec_succ hc hA hz hs hn := full_natRec_succ H henv hc hA hz hs hn
  adequate f ρ := f.adequate H henv ρ

end

instance : ObjEnv (full natEnv) := .full hasNat_natEnv natEnv_ordered

end Obj

end Incomplete
