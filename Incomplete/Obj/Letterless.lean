import Incomplete.Obj.Solovay
import Incomplete.Modal.Letterless

/-!
# Letterless sentences

The realization of a letterless formula does not depend on the realization of variables
(`Modal.real_letterless`). For a `halts`-sound well-formed extension of `natEnv` that proves `dneS`:

- `provable_iff_lvl`: the theory proves `A`'s realization iff `A` holds at every level of the
  tower, iff the Boolean `Modal.dec A` (`provable_iff_dec`). The implication from the levels
  needs only `dneS` (`provable_of_lvl`).
- `tr_iff_lim`: `A`'s truth, `□` read as provability in `env` (`Modal.tr`), is its eventual value
  `Modal.lim A`.

With `halts`-soundness alone, each `□ⁿ⊥` is unprovable (`boxBot_unprovable`), and each
`□ⁿ⁺¹⊥ → □ⁿ⊥` is true and unprovable (`tr_boxBot_succ_imp`, `boxBot_succ_imp_unprovable`). At
`n = 0` this is `¬□⊥`, provably equivalent to `Con T` (`con_iff_real_neg_box`), and its
unprovability needs only consistency (`con_unprovable_letterless`).
-/

namespace Incomplete
open Lean4Lean Obj

namespace Modal

theorem real_letterless {T : Tables} {σ σ' : Nat → VExpr} :
    ∀ {A : Modal}, Letterless A → A.real T σ = A.real T σ'
  | var _, h => h.elim
  | bot, _ => rfl
  | imp A B, h => by
    show VExpr.forallE (A.real T σ) (B.real T σ) = .forallE (A.real T σ') (B.real T σ')
    rw [real_letterless (σ' := σ') h.1, real_letterless (σ' := σ') h.2]
  | box A, h => by
    show Prov T (A.real T σ) = Prov T (A.real T σ')
    rw [real_letterless (A := A) (σ' := σ') h]

/-- Truth of a letterless formula, with `□B` true when the theory proves `B`'s realization. -/
def tr (env : VEnv) (T : Tables) : Modal → Prop
  | var _ | bot => False
  | imp A B => tr env T A → tr env T B
  | box A => Provable env (A.real T fun _ => falseS)

end Modal

/-- `halts`-soundness gives consistency: `PR.succ .zero` never halts. -/
theorem HaltsSound.consistent {env : VEnv} (hwf : env.WF) (hext : natEnv ≤ env)
    (hS : HaltsSound env) : Consistent env := by
  intro hF
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  have hty : Typing.HasType env [] (halts (.succ .zero) 0) (.sort .zero) := by
    rw [halts_eq]; exact impTy (notHalts_prop this.hasNat this.ordered _ _) falseT
  obtain ⟨k, hk⟩ := hS _ _ (Thm.exfalso (Thm.ofProvable hF) hty).provable
  exact Nat.succ_ne_zero _ hk

/-- **Levels give provability.** If the theory proves `dneS`, a letterless formula that holds
at every level has a provable realization. -/
theorem provable_of_lvl (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) {A : Modal} (hA : A.Letterless)
    (h : ∀ n, Modal.lvl n A = true) (σ : Nat → VExpr) : Provable env (A.real T σ) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  rw [Modal.real_letterless hA (σ' := fun _ => falseS)]
  exact GL_sound env hwf hext hT hdne (fun _ => falseT) ((Modal.GL_iff_lvl hA).2 h)

/-- **Provability gives levels**, for a `halts`-sound theory that proves `dneS`. -/
theorem lvl_of_provable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (hA : A.Letterless) {σ : Nat → VExpr} (h : Provable env (A.real T σ)) :
    ∀ n, Modal.lvl n A = true := by
  refine (Modal.GL_iff_lvl hA).1 (Classical.byContradiction fun hn => ?_)
  obtain ⟨σ', -, hn'⟩ := GL_arith_complete env hwf hext hT hdne hS hn
  exact hn' (Modal.real_letterless hA ▸ h)

/-- **The letterless provability logic is the level tower.** -/
theorem provable_iff_lvl (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (hA : A.Letterless) (σ : Nat → VExpr) :
    Provable env (A.real T σ) ↔ ∀ n, Modal.lvl n A = true :=
  ⟨lvl_of_provable env hwf hext hT hdne hS hA, fun h => provable_of_lvl env hwf hext hT hdne hA h σ⟩

/-- Provability of letterless sentences is decided by the Boolean `Modal.dec`. -/
theorem provable_iff_dec (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) {A : Modal}
    (hA : A.Letterless) (σ : Nat → VExpr) :
    Provable env (A.real T σ) ↔ Modal.dec A = true :=
  (provable_iff_lvl env hwf hext hT hdne hS hA σ).trans Modal.dec_iff.symm

/-- **Truth is the limit** (Solovay's second theorem, letterless case). -/
theorem tr_iff_lim (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) (hS : HaltsSound env) :
    ∀ {A : Modal}, A.Letterless → (A.tr env T ↔ Modal.lim A = true)
  | .var _, h => h.elim
  | .bot, _ => by simp [Modal.tr, Modal.lim, Modal.bd]
  | .imp A B, h => by
    rw [Modal.lim_imp]
    have iA := tr_iff_lim env hwf hext hT hdne hS (A := A) h.1
    have iB := tr_iff_lim env hwf hext hT hdne hS (A := B) h.2
    show (A.tr env T → B.tr env T) ↔ _
    rw [iA, iB]; cases Modal.lim A <;> simp
  | .box A, h => by
    rw [Modal.lim_box]
    exact provable_iff_dec env hwf hext hT hdne hS (A := A) h _

/-- **Iterated consistency.** In a `halts`-sound theory, `□ⁿ⊥` is unprovable. -/
theorem boxBot_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hS : HaltsSound env) (σ : Nat → VExpr) :
    ∀ n, ¬Provable env ((Modal.boxBot n).real T σ)
  | 0 => HaltsSound.consistent hwf hext hS
  | n + 1 => fun h => boxBot_unprovable env hwf hext hT hS σ n
      (prov_sound (hasNat_natEnv.mono hext) hwf.ordered hT hS h)

/-- Löb's theorem: `□ⁿ⁺¹⊥ → □ⁿ⊥` is provable only with `□ⁿ⊥`. -/
theorem boxBot_succ_imp_unprovable_of (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    {T : Tables} (hT : TablesFor env T) {σ : Nat → VExpr} {n : Nat}
    (hn : ¬Provable env ((Modal.boxBot n).real T σ)) :
    ¬Provable env ((Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).real T σ) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  rw [Modal.real_letterless (Modal.boxBot_letterless n) (σ' := fun _ => falseS)] at hn
  rw [Modal.real_letterless (A := .imp _ _)
    ⟨Modal.boxBot_letterless (n + 1), Modal.boxBot_letterless n⟩ (σ' := fun _ => falseS)]
  exact fun h => hn (loeb env hwf hext hT (Modal.realTy (env := env) (fun _ => falseTy) _) h)

/-- In a `halts`-sound theory, `□ⁿ⁺¹⊥ → □ⁿ⊥` is unprovable. -/
theorem boxBot_succ_imp_unprovable (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    {T : Tables} (hT : TablesFor env T) (hS : HaltsSound env) (σ : Nat → VExpr) (n : Nat) :
    ¬Provable env ((Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).real T σ) :=
  boxBot_succ_imp_unprovable_of env hwf hext hT (boxBot_unprovable env hwf hext hT hS σ n)

/-- In a `halts`-sound theory, `□ⁿ⁺¹⊥ → □ⁿ⊥` is true. -/
theorem tr_boxBot_succ_imp (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hS : HaltsSound env) (n : Nat) :
    (Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).tr env T :=
  fun h => (boxBot_unprovable env hwf hext hT hS _ n h).elim

/-- `¬□⊥`, the case `n = 0` of `□ⁿ⁺¹⊥ → □ⁿ⊥`, is provably equivalent to `Con T`. -/
theorem con_iff_real_neg_box (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) (T : Tables)
    (σ : Nat → VExpr) :
    Provable env (iff (Con T) ((Modal.imp (Modal.boxBot 1) (Modal.boxBot 0)).real T σ)) := by
  have h := con_iff_not_prov (hasNat_natEnv.mono hext) hwf.ordered T
  rwa [Obj.neg, imp_eq_forallE falseS_closed] at h

/-- **Second incompleteness**, as the case `n = 0`: a consistent theory does not prove
`Con T`, since it does not prove `¬□⊥`. -/
theorem con_unprovable_letterless (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env)
    {T : Tables} (hT : TablesFor env T) (hC : Consistent env) : ¬Provable env (Con T) := by
  have : ObjEnv env := .full (hasNat_natEnv.mono hext) hwf.ordered
  have hty := Modal.realTy (env := env) (T := T) (fun _ => falseT)
    (Modal.imp (Modal.boxBot 1) (Modal.boxBot 0))
  have hi := Thm.iffE1 (env := env) (ConT this.hasNat this.ordered) hty
    (con_iff_real_neg_box env hwf hext T fun _ => falseS)
  exact fun h => boxBot_succ_imp_unprovable_of env hwf hext hT (σ := fun _ => falseS) (n := 0) hC
    (hi.mp h).provable

end Incomplete
