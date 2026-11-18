/-!
# Modal formulas and the provability logic GL

`Modal` formulas are built from variables, `⊥`, `→` and `□`. `Modal.Deriv cl` is the Hilbert
system with the axioms `A → B → A`, `(A → B → C) → (A → B) → A → C`, `⊥ → A`, K
(`□(A → B) → □A → □B`) and Löb (`□(□A → A) → □A`), the rules modus ponens and necessitation, and,
when `cl` holds, double-negation elimination `¬¬A → A`: `GL` is `Deriv true` and its
intuitionistic fragment `iGL` is `Deriv false`.
-/

namespace Incomplete

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

end Modal

end Incomplete
