import Incomplete.Obj.Derivability

/-!
# Arithmetical soundness of GL

Modal formulas (`Modal`) are built from variables, `⊥`, `→` and `□`. `Modal.Deriv cl` is the
Hilbert system with the axioms `A → B → A`, `(A → B → C) → (A → B) → A → C`, `⊥ → A`, K
(`□(A → B) → □A → □B`) and Löb (`□(□A → A) → □A`), the rules modus ponens and necessitation, and,
when `cl` holds, double-negation elimination `¬¬A → A`: `GL` is `Deriv true` and its
intuitionistic fragment `iGL` is `Deriv false`. A realization `σ` sends variables to closed
propositions; `A.real T σ` sends `⊥` to `falseS`, `→` to the object implication and `□` to
`Prov T`.

Every `iGL` theorem is provable under every realization (`iGL_sound`); every `GL` theorem is, when
the theory proves double-negation elimination `dneS` (`GL_sound`). K is D2 (`prov_mp`), the Löb
axiom is formalized Löb (`loeb_int`), and necessitation is D1 (`prov_of_provable`).

`fairbot`: two closed propositions `A ↔ Prov T B` and `B ↔ Prov T A` are both provable.
-/

namespace Incomplete
open Lean4Lean Obj

/-- Double-negation elimination, `∀ p : Prop, ¬¬p → p`. -/
def dneS : VExpr := .forallE (.sort .zero) (imp (neg (neg (.bvar 0))) (.bvar 0))

/-- Modal formulas: variables, `⊥`, `→` and `□`. -/
inductive Modal where
  | var (n : Nat)
  | bot
  | imp (A B : Modal)
  | box (A : Modal)

namespace Modal

/-- `¬A`. -/
def neg (A : Modal) : Modal := imp A bot
/-- `⊤`. -/
def top : Modal := neg bot
/-- `A ∨ B`. -/
def or (A B : Modal) : Modal := imp (neg A) B
/-- `A ∧ B`. -/
def and (A B : Modal) : Modal := neg (imp A (neg B))
/-- `A ↔ B`. -/
def iff (A B : Modal) : Modal := and (imp A B) (imp B A)
/-- `◇A`. -/
def dia (A : Modal) : Modal := neg (box (neg A))

/-- Derivability in `GL` (`cl = true`) and in its intuitionistic fragment (`cl = false`). -/
inductive Deriv (cl : Bool) : Modal → Prop
  | k1 (A B : Modal) : Deriv cl (imp A (imp B A))
  | s (A B C : Modal) : Deriv cl (imp (imp A (imp B C)) (imp (imp A B) (imp A C)))
  | efq (A : Modal) : Deriv cl (imp bot A)
  | dne (A : Modal) : cl = true → Deriv cl (imp (neg (neg A)) A)
  | k (A B : Modal) : Deriv cl (imp (box (imp A B)) (imp (box A) (box B)))
  | loeb (A : Modal) : Deriv cl (imp (box (imp (box A) A)) (box A))
  | mp {A B : Modal} : Deriv cl (imp A B) → Deriv cl A → Deriv cl B
  | nec {A : Modal} : Deriv cl A → Deriv cl (box A)

/-- `GL ⊢ A`. -/
abbrev GL : Modal → Prop := Deriv true

/-- `iGL ⊢ A`: `GL` without double-negation elimination. -/
abbrev iGL : Modal → Prop := Deriv false

/-- The realization of `A` at `σ`: `⊥` is `falseS`, `→` the object implication, `□` is
`Prov T`. -/
noncomputable def real (T : Tables) (σ : Nat → VExpr) : Modal → VExpr
  | var n => σ n
  | bot => falseS
  | imp A B => .forallE (real T σ A) (real T σ B)
  | box A => Prov T (real T σ A)

end Modal

namespace Obj
section
variable {env : VEnv} [E : ObjEnv env] {X Y Z : VExpr}

theorem lookup_closed (hX : X.ClosedN) :
    ∀ {Γ : List VExpr} {i : Nat}, Γ[i]? = some X → Lookup Γ i X
  | Y :: Γ, 0, h => by
    cases (Option.some.inj h)
    have : Lookup (X :: Γ) 0 X.lift := .zero
    rwa [hX.lift_eq] at this
  | Y :: Γ, i + 1, h => by
    have : Lookup (Y :: Γ) (i + 1) X.lift := .succ (lookup_closed hX (Γ := Γ) (i := i) h)
    rwa [hX.lift_eq] at this

theorem closedN_of_ty (h : env.HasType 0 [] X (.sort .zero)) : X.ClosedN :=
  h.closedN E.ordered trivial

variable (hX : env.HasType 0 [] X (.sort .zero)) (hY : env.HasType 0 [] Y (.sort .zero))
  (hZ : env.HasType 0 [] Z (.sort .zero))

include hX hY in
theorem imp_k1 : Thm env [] (imp X (imp Y X)) := by
  refine Thm.intro hX ?_
  rw [(closedN_of_ty (impTy hY hX)).lift_eq]
  refine Thm.intro (closedTy hY) ?_
  rw [(closedN_of_ty hX).lift_eq]
  exact Thm.hyp (lookup_closed (closedN_of_ty hX) (i := 1) rfl)

include hX hY hZ in
theorem imp_s : Thm env [] (imp (imp X (imp Y Z)) (imp (imp X Y) (imp X Z))) := by
  have hXc := closedN_of_ty hX
  have hYc := closedN_of_ty hY
  have hZc := closedN_of_ty hZ
  have hXY := closedN_of_ty (impTy hX hY)
  have hXYZ := closedN_of_ty (impTy hX (impTy hY hZ))
  refine Thm.intro (impTy hX (impTy hY hZ)) ?_
  rw [(closedN_of_ty (impTy (impTy hX hY) (impTy hX hZ))).lift_eq]
  refine Thm.intro (closedTy (impTy hX hY)) ?_
  rw [(closedN_of_ty (impTy hX hZ)).lift_eq]
  refine Thm.intro (closedTy hX) ?_
  rw [hZc.lift_eq]
  have h1 : Thm env [X, imp X Y, imp X (imp Y Z)] (imp X (imp Y Z)) :=
    Thm.hyp (lookup_closed hXYZ (i := 2) rfl)
  have h2 : Thm env [X, imp X Y, imp X (imp Y Z)] (imp X Y) :=
    Thm.hyp (lookup_closed hXY (i := 1) rfl)
  have h3 : Thm env [X, imp X Y, imp X (imp Y Z)] X := Thm.hyp (lookup_closed hXc (i := 0) rfl)
  exact (h1.mp h3).mp (h2.mp h3)

include hX in
theorem imp_efq : Thm env [] (imp falseS X) := by
  refine Thm.intro falseTy ?_
  exact Thm.exfalso ((Thm.hyp .zero).cast rfl) (weakTy hX)

omit E in
include hX in
theorem imp_dne (h : Provable env dneS) : Thm env [] (imp (neg (neg X)) X) := by
  have := Thm.pallE (h : Thm env [] dneS) hX
  simp only [obj_simp] at this
  exact this

include hX hZ in
theorem imp_trans (h1 : Thm env [] (imp X Y)) (h2 : Thm env [] (imp Y Z)) :
    Thm env [] (imp X Z) := by
  refine Thm.intro hX ?_
  rw [(closedN_of_ty hZ).lift_eq]
  exact h2.weak0.mp (h1.weak0.mp (Thm.hyp (lookup_closed (closedN_of_ty hX) (i := 0) rfl)))

/-- D1 and D2: a provable implication between closed propositions is one between their
provability sentences. -/
theorem prov_imp {T : Tables} (hT : TablesFor env T) (hYc : Y.ClosedN)
    (h : Thm env [] (imp X Y)) : Thm env [] (imp (Prov T X) (Prov T Y)) :=
  (prov_mp hYc).mp (prov_of_provable E.hasNat E.ordered hT h.provable)

end
end Obj

namespace Modal
open Obj

section
variable {env : VEnv} [E : ObjEnv env] {T : Tables} {σ : Nat → VExpr}

theorem realTy (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero)) :
    ∀ A : Modal, env.HasType 0 [] (A.real T σ) (.sort .zero)
  | var n => hσ n
  | bot => falseTy
  | imp A B => by
    have h := impTy (realTy hσ A) (realTy hσ B)
    rwa [imp_eq_forallE (closedN_of_ty (realTy hσ B))] at h
  | box A => ProvTy T _

theorem real_imp (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero)) (A B : Modal) :
    (imp A B).real T σ = Obj.imp (A.real T σ) (B.real T σ) :=
  (imp_eq_forallE (closedN_of_ty (realTy hσ B))).symm

theorem real_box (A : Modal) : (box A).real T σ = Prov T (A.real T σ) := rfl
theorem real_bot : bot.real T σ = falseS := rfl

/-- **Soundness**, internally: `Deriv cl A` gives a proof of `A`'s realization, given
double-negation elimination when `cl` holds. -/
theorem deriv_sound (hT : TablesFor env T) (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero))
    {cl : Bool} (hcl : cl = true → Provable env dneS) {A : Modal} (h : Deriv cl A) :
    Thm env [] (A.real T σ) := by
  have ty := realTy (T := T) hσ
  induction h with
  | k1 A B =>
    simp only [real_imp hσ]; exact imp_k1 (ty A) (ty B)
  | s A B C =>
    simp only [real_imp hσ]; exact imp_s (ty A) (ty B) (ty C)
  | efq A =>
    simp only [real_imp hσ, real_bot]; exact imp_efq (ty A)
  | dne A h =>
    simp only [neg, real_imp hσ, real_bot]; exact imp_dne (ty A) (hcl h)
  | k A B =>
    simp only [real_imp hσ, real_box]; exact prov_mp (closedN_of_ty (ty B))
  | loeb A =>
    simp only [real_imp hσ, real_box]; exact loeb_int hT (closedN_of_ty (ty A))
  | mp _ _ ih1 ih2 =>
    rw [real_imp hσ] at ih1; exact ih1.mp ih2
  | nec _ ih =>
    exact prov_of_provable E.hasNat E.ordered hT ih.provable

end

end Modal

/-- **Arithmetical soundness of GL.** If the theory proves double-negation elimination, every
theorem of `GL` is provable under every realization by closed propositions, with `□` read as
`Prov T`. -/
theorem GL_sound (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) (hdne : Provable env dneS) {σ : Nat → VExpr}
    (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero)) {A : Modal} (h : Modal.GL A) :
    Provable env (A.real T σ) := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  exact (Modal.deriv_sound hT hσ (fun _ => hdne) h).provable

/-- **Arithmetical soundness of iGL**: every theorem of `GL` derived without double-negation
elimination is provable under every realization, in any well-formed extension of `natEnv`. -/
theorem iGL_sound (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {σ : Nat → VExpr} (hσ : ∀ n, env.HasType 0 [] (σ n) (.sort .zero))
    {A : Modal} (h : Modal.iGL A) : Provable env (A.real T σ) := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  exact (Modal.deriv_sound (cl := false) hT hσ (fun h => Bool.noConfusion h) h).provable

/-- **FairBot.** Closed propositions `A` and `B` with `A ↔ Prov T B` and `B ↔ Prov T A` are both
provable: `Prov T A → B → … → Prov T B → A`, so Löb's theorem gives `A`, and then `B`. -/
theorem fairbot (env : VEnv) (hwf : env.WF) (hext : natEnv ≤ env) {T : Tables}
    (hT : TablesFor env T) {A B : VExpr} (hA : env.HasType 0 [] A (.sort .zero))
    (hB : env.HasType 0 [] B (.sort .zero)) (hAB : Provable env (A ↔ₒ Prov T B))
    (hBA : Provable env (B ↔ₒ Prov T A)) : Provable env A ∧ Provable env B := by
  have : ObjEnv env := ⟨hasNat_natEnv.mono hext, hwf.ordered⟩
  have hPA := ProvTy (env := env) (Γ := []) T A
  have hPB := ProvTy (env := env) (Γ := []) T B
  have a1 : Thm env [] (imp (Prov T B) A) := Thm.iffE2 hA hPB hAB
  have b1 : Thm env [] (imp (Prov T A) B) := Thm.iffE2 hB hPA hBA
  have h1 : Thm env [] (imp (Prov T A) (Prov T B)) :=
    imp_trans hPA hPB (prov_prov hT A) (prov_imp hT (closedN_of_ty hB) b1)
  have h2 : Thm env [] (imp (Prov T A) A) := imp_trans hPA hA h1 a1
  rw [imp_eq_forallE (closedN_of_ty hA)] at h2
  have pA := loeb env hwf hext hT hA h2
  exact ⟨pA, (b1.mp (prov_of_provable this.hasNat this.ordered hT pA)).provable⟩

end Incomplete
