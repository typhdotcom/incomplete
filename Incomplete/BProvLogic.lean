import Incomplete.ClEnv
import Incomplete.Obj.BChecker
import Incomplete.Obj.Solovay
import Incomplete.Obj.Letterless

/-!
# The provability logic of the classical fragment, without hypotheses

`clEnv` is `natEnv` with the axiom `dneS`. Its fragment `BProvable clEnv` (sorts `Prop` and
`Type`, no projection rules) proves `dneS`, and by the set model it is consistent and sound for
`halts` sentences (`ClEnv.lean`). Its provability is internalized by `BProv P`, the sentence that
some certificate passes the fragment's checker `bchkT clT` as a proof of `P`, and `□` is realized
as `BProv` (`Modal.breal`). With every hypothesis discharged:

- `GL_iff_bprovable`: `GL` is the provability logic of the fragment;
- `bprovable_iff_lvl`: a letterless sentence is provable iff it holds at every level;
- `btr_iff_lim`: a letterless sentence is true, `□B` read as provability of `B`'s realization,
  iff its limit is `true`;
- `bcon_iterated`: each `□ⁿ⁺¹⊥ → □ⁿ⊥` is true and unprovable, and each `□ⁿ⊥` is unprovable.
-/

namespace Incomplete
open Lean4Lean Obj

instance : ObjEnv (bounded clEnv) := .bounded hasNat_clEnv clEnv_ordered

/-- **Bounded provability** in `clEnv`, as a sentence: some certificate passes the fragment's
checker as a proof of `P`. -/
noncomputable def BProv (P : VExpr) : VExpr := ProvC (bchkT clT) P

/-- The realization of `A` at `σ` with `□` read as `BProv`. -/
noncomputable def Modal.breal (σ : Nat → VExpr) (A : Modal) : VExpr := A.realC (bchkT clT) σ

theorem Modal.breal_box (σ : Nat → VExpr) (A : Modal) : (box A).breal σ = BProv (A.breal σ) := rfl

theorem bchk_isChecker : IsChecker (bounded clEnv) (bchkT clT) := .bounded clEnv_tables

theorem bchk_sound (P : VExpr) (k : Nat) (h : bchkNum clT (encExpr P) k = 0) :
    Thm (bounded clEnv) [] P :=
  bchkNum_sound clEnv_tables h

/-- **Arithmetical soundness of GL** for the fragment of `clEnv`. -/
theorem GL_bsound {σ : Nat → VExpr} (hσ : ∀ n, BDefEq clEnv [] (σ n) (σ n) (.sort .zero))
    {A : Modal} (h : Modal.GL A) : BProvable clEnv (A.breal σ) :=
  Modal.deriv_sound (env := bounded clEnv) bchk_isChecker hσ (fun _ => clEnv_dne) h

/-- **Arithmetical completeness of GL** for the fragment of `clEnv`. -/
theorem GL_barith_complete {A : Modal} (h : ¬Modal.GL A) :
    ∃ σ : Nat → VExpr, (∀ n, BDefEq clEnv [] (σ n) (σ n) (.sort .zero)) ∧
      ¬BProvable clEnv (A.breal σ) :=
  arith_complete (env := bounded clEnv) bchk_isChecker (bchkT_computes clT) bchk_sound clEnv_dne
    (fun _ _ h => clEnv_bhaltsSound h) h

/-- **GL is the provability logic of the classical fragment**: a modal formula is a theorem of
`GL` exactly when the fragment of `clEnv` proves it under every realization by closed
propositions of the fragment, with `□` read as bounded provability `BProv`. No hypothesis
remains. -/
theorem GL_iff_bprovable {A : Modal} :
    Modal.GL A ↔ ∀ σ : Nat → VExpr, (∀ n, BDefEq clEnv [] (σ n) (σ n) (.sort .zero)) →
      BProvable clEnv (A.breal σ) :=
  ⟨fun h _ hσ => GL_bsound hσ h, fun h => Classical.byContradiction fun hA =>
    let ⟨σ, hσ, hn⟩ := GL_barith_complete hA
    hn (h σ hσ)⟩

theorem Modal.breal_letterless {σ σ' : Nat → VExpr} {A : Modal} (hA : A.Letterless) :
    A.breal σ = A.breal σ' := realC_letterless hA

/-- **The letterless provability logic of the fragment is the level tower.** -/
theorem bprovable_iff_lvl {A : Modal} (hA : A.Letterless) (σ : Nat → VExpr) :
    BProvable clEnv (A.breal σ) ↔ ∀ n, Modal.lvl n A = true := by
  rw [Modal.breal_letterless hA (σ' := fun _ => falseS), ← Modal.GL_iff_lvl hA]
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨σ', -, hn'⟩ := GL_barith_complete hn
    exact hn' (Modal.breal_letterless hA ▸ h)
  · exact GL_bsound (σ := fun _ => falseS) (fun _ => falseTy (env := bounded clEnv))

/-- Provability of letterless sentences in the fragment is decided by `Modal.dec`. -/
theorem bprovable_iff_dec {A : Modal} (hA : A.Letterless) (σ : Nat → VExpr) :
    BProvable clEnv (A.breal σ) ↔ Modal.dec A = true :=
  (bprovable_iff_lvl hA σ).trans Modal.dec_iff.symm

/-- Truth of a letterless formula, with `□B` true when the fragment proves `B`'s realization. -/
def Modal.btr : Modal → Prop
  | var _ | bot => False
  | imp A B => btr A → btr B
  | box A => BProvable clEnv (A.breal fun _ => falseS)

/-- **Truth is the limit**, for the fragment of `clEnv`. -/
theorem btr_iff_lim : ∀ {A : Modal}, A.Letterless → (A.btr ↔ Modal.lim A = true)
  | .var _, h => h.elim
  | .bot, _ => by simp [Modal.btr, Modal.lim, Modal.bd]
  | .imp A B, h => by
    rw [Modal.lim_imp]
    have iA := btr_iff_lim (A := A) h.1
    have iB := btr_iff_lim (A := B) h.2
    show (A.btr → B.btr) ↔ _
    rw [iA, iB]; cases Modal.lim A <;> simp
  | .box A, h => by
    rw [Modal.lim_box]
    exact bprovable_iff_dec (A := A) h _

/-- **Iterated consistency of the fragment.** For every `n`, `□ⁿ⊥` is unprovable, and
`□ⁿ⁺¹⊥ → □ⁿ⊥` is true and unprovable; at `n = 0` the latter is `¬□⊥`, the consistency of the
fragment as `¬BProv ⊥`. -/
theorem bcon_iterated (σ : Nat → VExpr) (n : Nat) :
    ¬BProvable clEnv ((Modal.boxBot n).breal σ) ∧
      (Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).btr ∧
      ¬BProvable clEnv ((Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).breal σ) := by
  have hl : (Modal.imp (Modal.boxBot (n + 1)) (Modal.boxBot n)).Letterless :=
    ⟨Modal.boxBot_letterless (n + 1), Modal.boxBot_letterless n⟩
  obtain ⟨hlim, hGL⟩ := Modal.boxBot_succ_imp n
  refine ⟨fun h => ?_, (btr_iff_lim hl).2 hlim, fun h => hGL ?_⟩
  · have := (bprovable_iff_lvl (Modal.boxBot_letterless n) σ).1 h n
    rw [Modal.lvl_boxBot] at this
    simp at this
  · exact (Modal.GL_iff_lvl hl).2 ((bprovable_iff_lvl hl σ).1 h)

end Incomplete
