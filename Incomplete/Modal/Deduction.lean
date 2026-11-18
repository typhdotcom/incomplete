import Incomplete.Modal.Basic

/-!
# Derivations from hypotheses in GL

`Der Γ A`: `A` follows from the hypotheses `Γ` by modus ponens over the theorems of `GL`. The
deduction theorem (`Der.deduction`), weakening (`Der.mono`), cut (`Der.cut`), boxing a
derivation (`Der.box`, from K and necessitation) and the 4 axiom `□A → □□A` (`GL_four`, from
Löb). `Con Γ`: `⊥` does not follow from `Γ`; `con_or` is the Lindenbaum step.
-/

namespace Incomplete
namespace Modal

/-- `A` follows from `Γ` by modus ponens over `GL`. -/
inductive Der (Γ : List Modal) : Modal → Prop
  | ax {A : Modal} : GL A → Der Γ A
  | hyp {A : Modal} : A ∈ Γ → Der Γ A
  | mp {A B : Modal} : Der Γ (imp A B) → Der Γ A → Der Γ B

/-- `Γ` is consistent. -/
def Con (Γ : List Modal) : Prop := ¬Der Γ bot

theorem GL_id (A : Modal) : GL (imp A A) :=
  .mp (.mp (.s A (imp A A) A) (.k1 A (imp A A))) (.k1 A A)

namespace Der
variable {Γ Δ : List Modal} {A B C : Modal}

theorem mono (h : Der Γ A) (hs : ∀ x ∈ Γ, x ∈ Δ) : Der Δ A := by
  induction h with
  | ax h => exact ax h
  | hyp h => exact hyp (hs _ h)
  | mp _ _ ih1 ih2 => exact mp ih1 ih2

theorem cut (h : Der Δ A) (hs : ∀ x ∈ Δ, Der Γ x) : Der Γ A := by
  induction h with
  | ax h => exact ax h
  | hyp h => exact hs _ h
  | mp _ _ ih1 ih2 => exact mp ih1 ih2

theorem deduction (h : Der (A :: Γ) B) : Der Γ (imp A B) := by
  induction h with
  | ax h => exact mp (ax (.k1 _ _)) (ax h)
  | @hyp B h =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ax (GL_id _)
    · exact mp (ax (.k1 _ _)) (hyp h)
  | mp _ _ ih1 ih2 => exact mp (mp (ax (.s _ _ _)) ih1) ih2

theorem of_nil (h : Der [] A) : GL A := by
  induction h with
  | ax h => exact h
  | hyp h => nomatch h
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

theorem absurd (h1 : Der Γ A) (h2 : Der Γ (neg A)) : Der Γ C :=
  mp (ax (.efq C)) (mp h2 h1)

theorem dne (h : Der Γ (neg (neg A))) : Der Γ A := mp (ax (.dne A rfl)) h

theorem box : ∀ {Γ : List Modal} {A : Modal}, Der Γ A → Der (Γ.map Modal.box) (Modal.box A)
  | [], _, h => ax (.nec h.of_nil)
  | C :: Γ, _, h => by
    have := box (deduction h)
    exact mp (mp (ax (.k _ _)) (this.mono fun x hx => .tail _ hx)) (hyp (.head _))

end Der

/-- The 4 axiom, from Löb at `A ∧ □A`. -/
theorem GL_four (A : Modal) : GL (imp (box A) (box (box A))) := by
  let D := and A (box A)
  -- `A, □D ⊢ D`, hence `A ⊢ □D → D`.
  have h1 : Der [box D, A] D := by
    have hA : Der [box D, A] (box A) := by
      have : GL (imp D A) := by
        refine Der.of_nil (Der.deduction (Der.dne (Der.deduction ?_)))
        refine Der.mp (Der.hyp (.tail _ (.head _))) (Der.deduction (Der.deduction ?_))
        exact Der.absurd (Der.hyp (.tail _ (.head _))) (Der.hyp (.tail _ (.tail _ (.head _))))
      exact Der.mp (Der.mp (Der.ax (.k _ _)) (Der.ax (.nec this))) (Der.hyp (.head _))
    refine Der.deduction ?_
    exact Der.mp (Der.mp (Der.hyp (.head _)) (Der.hyp (.tail _ (.tail _ (.head _)))))
      (hA.mono fun x hx => .tail _ hx)
  have h2 : Der [box A] (box D) :=
    Der.mp (Der.ax (.loeb D)) (by simpa using Der.box (Der.deduction h1))
  have hBD : GL (imp D (box A)) := by
    refine Der.of_nil (Der.deduction (Der.dne (Der.deduction ?_)))
    refine Der.mp (Der.hyp (.tail _ (.head _))) (Der.deduction (Der.deduction ?_))
    exact Der.absurd (Der.hyp (.head _)) (Der.hyp (.tail _ (.tail _ (.head _))))
  exact Der.of_nil (Der.deduction
    (Der.mp (Der.mp (Der.ax (.k _ _)) (Der.ax (.nec hBD))) h2))

/-- **Lindenbaum step**: a consistent `Γ` stays consistent with `A` or with `¬A`. -/
theorem con_or {Γ : List Modal} (h : Con Γ) (A : Modal) : Con (A :: Γ) ∨ Con (neg A :: Γ) := by
  refine Classical.or_iff_not_imp_left.2 fun h1 h2 => h ?_
  exact Der.mp (Der.deduction h2) (Der.deduction (Classical.not_not.1 h1))

end Modal
end Incomplete
