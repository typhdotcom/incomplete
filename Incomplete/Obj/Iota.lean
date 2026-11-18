import Incomplete.Obj.Core

/-!
# Iota and `Nat.rec` congruence in any context

`HasNat.iota_zero'` and `iota_succ'` need the context to be well formed, which `Thm` does not
record. At a closed motive the rules hold in the closed context of their own arguments, so
weakening and instantiating them gives them in every context (`natRec_zero`, `natRec_succ`).
`natRec_congr3` is congruence in all three arguments.
-/

namespace Incomplete.Obj
open Lean4Lean
open VExpr VEnv

section
variable {env : VEnv} [E : ObjEnv env] {Γ : List VExpr} {A z z' s s' n n' : VExpr}

/-- The step type `Nat → A → A`. -/
abbrev stepT (A : VExpr) : VExpr := .forallE nat (.forallE A A)

theorem stepT_T (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero))) :
    env.HasType 0 Γ (stepT A) (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallE natTy (.forallE (hA _) (hA _))

omit E in
theorem stepT_inert (hI : Inert A) : Inert (stepT A) :=
  ⟨fun _ _ => by simp [VExpr.liftN, hI.liftN], fun _ _ => by simp [VExpr.inst, hI.inst],
   fun _ => by simp [VExpr.subst, hI.subst]⟩

theorem natRec_zero (hc : A.ClosedN) (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 Γ z A) (hs : env.HasType 0 Γ s (stepT A)) :
    env.IsDefEq 0 Γ (natRec A z s zero) z A := by
  have hI := Inert.ofClosed hc
  have hΔ : OnCtx [stepT A, A] (env.IsType 0) := ⟨⟨trivial, _, hA _⟩, _, stepT_T hA⟩
  have hz0 : env.HasType 0 [stepT A, A] (.bvar 1) A := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.succ (A := stepT A) (Lookup.zero (Γ := [])
      (ty := A))); simpa only [hI.liftN] using this
  have hs0 : env.HasType 0 [stepT A, A] (.bvar 0) (stepT A) := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.zero (Γ := [A]) (ty := stepT A))
    simpa only [(stepT_inert hI).liftN] using this
  have h := E.hasNat.iota_zero' E.ordered hΔ hI hA hz0 hs0
  have hcl : CtxClosed [stepT A, A] :=
    ⟨⟨trivial, hc⟩, ⟨trivial, hc.mono (Nat.zero_le _), hc.mono (Nat.zero_le _)⟩⟩
  have h := h.weakR E.ordered hcl Γ
  have hs' : env.HasType 0 (A :: Γ) s.lift (stepT A) := by
    have := weakTy (B := A) hs; simpa only [(stepT_inert hI).liftN] using this
  have h := h.instN E.ordered hs' .zero
  have h := h.instN E.ordered hz .zero
  simpa [natRec, motive, VExpr.inst, hI.inst, inst_lift] using h

theorem natRec_succ (hc : A.ClosedN) (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.HasType 0 Γ z A) (hs : env.HasType 0 Γ s (stepT A)) (hn : env.HasType 0 Γ n nat) :
    env.IsDefEq 0 Γ (natRec A z s (S n)) (.app (.app s n) (natRec A z s n)) A := by
  have hI := Inert.ofClosed hc
  have hΔ : OnCtx [nat, stepT A, A] (env.IsType 0) :=
    ⟨⟨⟨trivial, _, hA _⟩, _, stepT_T hA⟩, _, natTy⟩
  have hz0 : env.HasType 0 [nat, stepT A, A] (.bvar 2) A := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.succ (A := nat) (Lookup.succ (A := stepT A)
      (Lookup.zero (Γ := []) (ty := A)))); simpa only [hI.liftN] using this
  have hs0 : env.HasType 0 [nat, stepT A, A] (.bvar 1) (stepT A) := by
    have := HasType.bvar (env := env) (U := 0) (Lookup.succ (A := nat)
      (Lookup.zero (Γ := [A]) (ty := stepT A)))
    simpa only [(stepT_inert hI).liftN] using this
  have h := E.hasNat.iota_succ' E.ordered hΔ hI hA hz0 hs0 (.bvar .zero)
  have hcl : CtxClosed [nat, stepT A, A] :=
    ⟨⟨⟨trivial, hc⟩, ⟨trivial, hc.mono (Nat.zero_le _), hc.mono (Nat.zero_le _)⟩⟩,
      trivial⟩
  have h := h.weakR E.ordered hcl Γ
  have hn' : env.HasType 0 (stepT A :: A :: Γ) n.lift.lift nat := weakTy (weakTy hn)
  have hs' : env.HasType 0 (A :: Γ) s.lift (stepT A) := by
    have := weakTy (B := A) hs; simpa only [(stepT_inert hI).liftN] using this
  have h := h.instN E.ordered hn' .zero
  have h := h.instN E.ordered hs' .zero
  have h := h.instN E.ordered hz .zero
  simpa [natRec, motive, S, VExpr.inst, hI.inst, inst_lift] using h

theorem natRec_congr3 (hc : A.ClosedN) (hA : ∀ Γ, env.HasType 0 Γ A (.sort (.succ .zero)))
    (hz : env.IsDefEq 0 Γ z z' A) (hs : env.IsDefEq 0 Γ s s' (stepT A))
    (hn : env.IsDefEq 0 Γ n n' nat) :
    env.IsDefEq 0 Γ (natRec A z s n) (natRec A z' s' n') A := by
  have hI := Inert.ofClosed hc
  have N := E.hasNat.toNatConsts
  have hM : env.HasType 0 Γ (motive A) (.forallE nat (.sort (.succ .zero))) := .lam N.natT (hA _)
  have h0 : env.HasType 0 Γ (.const ``Nat.rec [.succ .zero]) (recTy.instL [.succ .zero]) :=
    .const E.hasNat.hRec (by simp [VLevel.WF]) rfl
  have h1 := HasType.app h0 hM
  have e1 : (VExpr.instL [.succ .zero] (.forallE Incomplete.zeroTy (.forallE succTy
      (.forallE nat (.app (.bvar 3) (.bvar 0)))))).inst (motive A) =
      .forallE (.app (motive A) zero) (.forallE
        (.forallE nat (.forallE (.app (motive A) (.bvar 0))
          (.app (motive A) (.app succ (.bvar 1)))))
        (.forallE nat (.app (motive A) (.bvar 0)))) := by
    simp [Incomplete.zeroTy, succTy, VExpr.instL, VExpr.inst, instVar, (Inert.motive hI).liftN]
  rw [e1] at h1
  have h2 := IsDefEq.appDF h1 (.defeqDF (motive_app hI hA N.zeroT).symm hz)
  simp only [VExpr.inst, (Inert.motive hI).inst] at h2
  have h3 := IsDefEq.appDF h2 (.defeqDF (succMinor_conv N hI hA) hs)
  simp only [VExpr.inst, (Inert.motive hI).inst] at h3
  have h4 := IsDefEq.appDF h3 hn
  simp [VExpr.inst, instVar, (Inert.motive hI).inst] at h4
  exact .defeqDF (motive_app hI hA hn.hasType.1) h4

end

end Incomplete.Obj
