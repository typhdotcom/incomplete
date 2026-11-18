import Incomplete.Diag
import Incomplete.CheckPR
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Incompleteness, from consistency alone

For every environment extending `natEnv` that is `Checkable` — its constants and
definitional-equality rules and inductive types are listed by finite tables, and it is
ordered — consistency gives a true, unprovable non-halting sentence `notHalts d ⌜d⌝`, which
is also irrefutable if the theory's proofs of `halts` sentences are sound (`HaltsSound`).
-/

namespace Incomplete
open Lean4Lean

/-- What the proof checker needs of an environment. `TablesFor env T`: `env.constants` is the
first-match lookup in the finite list `T.consts`, and `env.defeqs` holds exactly of the members
of the finite list `T.rules`, and `env.inducts` is the first-match lookup in `T.inducts`.
`Ordered`: constants and rules were added well typed, which Σ₁-completeness uses. -/
structure Checkable (env : VEnv) : Prop where
  tables : ∃ T : Tables, TablesFor env T
  ordered : env.Ordered

/-- **Incompleteness.** A consistent checkable extension of `natEnv` does not prove the true
non-halting sentence `notHalts d ⌜d⌝` of some machine `d` on its own number; if the theory's
proofs of `halts` sentences are sound (`HaltsSound`), it does not refute it either. -/
theorem incomplete_of_consistent (env : VEnv) (hext : natEnv ≤ env) (hchk : Checkable env)
    (hC : Consistent env) :
    ∃ d : PR, ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
      (HaltsSound env → ¬Provable env (halts d d.code)) := by
  obtain ⟨T, hT⟩ := hchk.tables
  exact incomplete_of_check (hasNat_natEnv.mono hext) hchk.ordered
    (checkDecidable_of_tables hT) hC

end Incomplete
