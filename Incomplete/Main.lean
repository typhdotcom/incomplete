import Incomplete.Kleene
import Incomplete.Sentences
import Incomplete.NatDeclWF
import Incomplete.Encode

/-!
# Incompleteness of the object theory

For `natEnv`, or any ordered environment containing it: if the theory's proofs of the diagonal
`notHalts` sentences are enumerated by a machine (`DiagEnumerable`) and it does not prove `False`
(`Consistent`), some `notHalts d ⌜d⌝` is true and unprovable. If its proofs of `halts` sentences
are moreover sound (`HaltsSound`), it does not refute it either.

Σ₁-completeness (`halts_provable`) and the refutation of `False` from a proof of both `halts` and
`notHalts` (`refute`) are proved. The three hypotheses are what remains.
-/

namespace Lean4Lean.Incomplete

/-- A machine's number, as input to another: the number of its closed object-level function. -/
def PR.code (f : PR) : Nat := encExpr (fn f)

/-- The object theory does not prove `False`. -/
def Consistent (env : VEnv) : Prop := ¬Provable env falseS

/-- The object theory proves `halts f n` only when `f` halts on `n`: soundness for Σ₁
sentences, the theory's 1-consistency. -/
def HaltsSound (env : VEnv) : Prop := ∀ f n, Provable env (halts f n) → PR.Halts f n

/-- Some machine halts on `⌜f⌝` exactly when the object theory proves `notHalts f ⌜f⌝`: proofs
of the diagonal Π₁ sentences are recursively enumerable, in the machine model itself. -/
def DiagEnumerable (env : VEnv) : Prop :=
  ∃ d : PR, ∀ f : PR, d.Halts f.code ↔ Provable env (notHalts f f.code)

/-- The object theory proves `notHalts f n` only when `f` does not halt on `n`. -/
def NotHaltsSound (env : VEnv) : Prop := ∀ f n, Provable env (notHalts f n) → ¬PR.Halts f n

/-- The sound form: soundness for `notHalts` alone, with no assumption on `env`'s contents. -/
theorem true_unprovable {env : VEnv} (hE : DiagEnumerable env) (hS : NotHaltsSound env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) := by
  obtain ⟨d, hd⟩ := hE
  have hn : ¬Provable env (notHalts d d.code) := fun h => hS _ _ h ((hd d).2 h)
  exact ⟨d, fun h => hn ((hd d).1 h), hn⟩

/-- With `Nat`, consistency gives soundness for `notHalts`, by Σ₁-completeness. -/
theorem Consistent.notHaltsSound {env : VEnv} (H : HasNat env) (henv : env.Ordered)
    (hC : Consistent env) : NotHaltsSound env :=
  fun _ _ hp hh => hC (refute (halts_provable H henv hh) hp)

theorem incomplete {env : VEnv} (H : HasNat env) (henv : env.Ordered)
    (hE : DiagEnumerable env) (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code)) :=
  kleene PR.code PR.Halts (Provable env) halts notHalts
    (fun _ _ h => halts_provable H henv h) (fun _ _ h1 h2 => hC (refute h1 h2)) hE

/-- **Incompleteness** of the well-formed environment `natEnv` (`natEnv_wf`): `Nat` as
`VEnv.addInduct` adds it to the empty environment. -/
theorem natEnv_incomplete (hE : DiagEnumerable natEnv) (hC : Consistent natEnv) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable natEnv (notHalts d d.code) ∧
      (HaltsSound natEnv → ¬Provable natEnv (halts d d.code)) :=
  incomplete hasNat_natEnv natEnv_ordered hE hC

end Lean4Lean.Incomplete
