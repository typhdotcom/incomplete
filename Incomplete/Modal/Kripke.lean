import Incomplete.Modal.Basic

/-!
# Kripke semantics for GL

A Kripke model (`Kripke`) is an accessibility relation and a valuation on a type of worlds;
`M.Forces w A` is forcing, with `□A` forced at `w` when `A` is forced at every world `w` sees.

`Kripke.GL_sound`: every theorem of `GL` is forced at every world of every transitive model whose
accessibility relation is conversely well-founded.

`FinModel n` is a finite transitive irreflexive model on `Fin n` with Boolean relation and
valuation; `FinModel.eval` decides forcing (`eval_iff`). Such a relation is conversely
well-founded (`FinModel.wf`), so `FinModel.GL_sound`: every theorem of `GL` is forced at every
world of every `FinModel`.
-/

namespace Incomplete
namespace Modal

/-- A Kripke model: accessibility `R` and valuation `V` on worlds `α`. -/
structure Kripke (α : Type) where
  R : α → α → Prop
  V : α → Nat → Prop

namespace Kripke
variable {α : Type} (M : Kripke α)

/-- Forcing: `□A` holds at `w` when `A` holds at every `v` with `M.R w v`. -/
def Forces : α → Modal → Prop
  | w, var n => M.V w n
  | _, bot => False
  | w, imp A B => Forces w A → Forces w B
  | w, box A => ∀ v, M.R w v → Forces v A

/-- **Kripke soundness of GL**: on a transitive, conversely well-founded model, every theorem of
`GL` is forced everywhere. -/
theorem GL_sound (trans : ∀ {a b c}, M.R a b → M.R b c → M.R a c)
    (wf : WellFounded fun a b => M.R b a) {A : Modal} (h : GL A) : ∀ w, M.Forces w A := by
  induction h with
  | k1 => intro w h1 _; exact h1
  | s => intro w h1 h2 h3; exact h1 h3 (h2 h3)
  | efq => intro w h; exact h.elim
  | dne A _ => intro w h; exact Classical.byContradiction h
  | k => intro w h1 h2 v hv; exact h1 v hv (h2 v hv)
  | loeb A =>
    intro w h v hv
    induction v using wf.induction with
    | _ v ih => exact h v hv fun u hu => ih u hu (trans hv hu)
  | mp _ _ ih1 ih2 => intro w; exact ih1 w (ih2 w)
  | nec _ ih => intro w v _; exact ih v

end Kripke

/-- A finite transitive irreflexive Kripke model on `Fin n` with Boolean data. -/
structure FinModel (n : Nat) where
  R : Fin n → Fin n → Bool
  V : Fin n → Nat → Bool
  trans : ∀ {a b c}, R a b = true → R b c = true → R a c = true
  irrefl : ∀ a, R a a = false

namespace FinModel
variable {n : Nat} (M : FinModel n)

/-- `M` as a Kripke model. -/
def toKripke : Kripke (Fin n) := ⟨fun a b => M.R a b = true, fun a k => M.V a k = true⟩

/-- Forcing in `M`. -/
abbrev Forces : Fin n → Modal → Prop := M.toKripke.Forces

/-- `0` sees every other world. -/
def Rooted {n : Nat} (M : FinModel (n + 1)) : Prop := ∀ i : Fin (n + 1), i ≠ 0 → M.R 0 i = true

/-- Forcing, decided. -/
def eval : Fin n → Modal → Bool
  | w, var k => M.V w k
  | _, bot => false
  | w, imp A B => !eval w A || eval w B
  | w, box A => (List.finRange n).all fun v => !M.R w v || eval v A

theorem eval_iff : ∀ (w : Fin n) (A : Modal), M.eval w A = true ↔ M.Forces w A
  | w, var k => Iff.rfl
  | w, bot => by simp [eval, Kripke.Forces]
  | w, imp A B => by
    have := eval_iff w A; have := eval_iff w B
    simp only [eval, Kripke.Forces, Bool.or_eq_true, Bool.not_eq_true'] at *
    by_cases h : M.eval w A <;> simp_all
  | w, box A => by
    simp only [eval, Kripke.Forces, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.or_eq_true, Bool.not_eq_true']
    refine forall_congr' fun v => ?_
    have := eval_iff v A
    show _ ↔ (M.R w v = true → M.Forces v A)
    rw [← this]; cases M.R w v <;> simp

instance (w : Fin n) (A : Modal) : Decidable (M.Forces w A) :=
  decidable_of_iff _ (M.eval_iff w A)

theorem countP_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x → q x) → (∃ x ∈ l, q x ∧ ¬p x) →
      l.countP p < l.countP q
  | [], _, ⟨_, h, _⟩ => nomatch h
  | a :: l, hpq, ⟨x, hx, hq, hp⟩ => by
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left fun y hy => hpq y (.tail _ hy)
    simp only [List.countP_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp_all; omega
    · have := countP_lt (fun y hy => hpq y (.tail _ hy)) ⟨x, hx, hq, hp⟩
      have := hpq a (.head _)
      split <;> split <;> simp_all <;> omega

/-- The converse of `M.R` is well-founded: the number of successors drops along `M.R`. -/
theorem wf : WellFounded fun a b => M.R b a = true := by
  let f : Fin n → Nat := fun a => (List.finRange n).countP (M.R a ·)
  refine Subrelation.wf (r := InvImage (· < ·) f) (fun {a b} h => ?_) (InvImage.wf f Nat.lt_wfRel.wf)
  exact countP_lt (fun x _ hx => M.trans h hx) ⟨a, List.mem_finRange a, h, by simp [M.irrefl]⟩

/-- **Soundness of GL for finite transitive irreflexive models.** -/
theorem GL_sound {A : Modal} (h : GL A) (w : Fin n) : M.Forces w A :=
  M.toKripke.GL_sound M.trans M.wf h w

end FinModel

end Modal
end Incomplete
