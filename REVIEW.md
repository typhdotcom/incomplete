State: READY FOR REVIEW
Turn: reviewer
Candidate: yvnpokxyustvvsttkxvlmvwnspyllrwz / 7e6276a9902567f6f02fbd55586212322cfbe4d6

# Rosser and second incompleteness review

## Objective and meaning

Review the changes since the previous candidate `68cb58bf0c4d`: Rosser's
incompleteness theorem from consistency alone, internal arithmetic and proof
manipulation in `Incomplete/Obj`, the second incompleteness theorem for the
actual certificate checker, and their public documentation and tactics.

## Accepted foundation

- The proof system remains the pinned lean4lean fork's formal
  `VEnv.HasType` / `VEnv.IsDefEq` judgment. The upstream/fork distinction and
  specific dependencies are documented in `README.md`; preserve that account.
- Preserve the previously reviewed unconditional result for
  `BProvable natEnv`, the bounded, projection-free fragment, and the
  conditional full-theory Gödel–Kleene results.
- The new full-theory Rosser and second incompleteness statements assume
  consistency of a well-formed extension of `natEnv`. They do not establish
  full-theory consistency or kernel implementation correctness.
- `Con T` uses the existing checker `chkC T (fun _ => true)` through `conM T`.
  `con_true_iff` identifies its external non-halting interpretation with
  `Consistent env` for `TablesFor env T`.
- The source and axiom constraints in `AGENTS.md` remain in force.

## Submission

This candidate is the returned candidate `a9192d26a3bd` plus one commit that
changes only the `ohyp` elaborator in `Incomplete/Obj/Tactic.lean` (11
insertions, 4 deletions). No theorem statement, definition or other tactic
changed.

## Current drawers

### D1 — P2: `ohyp` stops before reaching a matching hypothesis

Status: resolved, awaiting review

Cause: each candidate was tried as `exact Thm.hyp (i := i) (by olookup)`. A
failing nested `by` block is recovered by the term elaborator, which logs the
error and admits the goal instead of throwing, so the first index whose lookup
got as far as a leftover equation was accepted and the search stopped there.

Change:

- Each candidate now runs as the tactic sequence
  `refine Thm.hyp (i := i) ?_; olookup; done` under `withoutRecover`, so any
  failure is an exception; the saved state is restored before the next index.
- The search covers every explicit entry of the goal's context: the number of
  `List.cons` cells of `Γ` (up to reducible unfolding), with no fixed limit.
  With an open tail (`A :: B :: Γ`) it covers the explicit prefix.
- A goal that is not `Thm env Γ P` is reported as such.

Closure evidence. The following file, checked with
`nix develop -c lake env lean`, elaborates with no errors or warnings. Every
check runs `ohyp` itself.

```lean
import Incomplete
open Incomplete Incomplete.Obj

example : Thm natEnv [falseS] falseS := by ohyp
example : Thm natEnv [nat, falseS] falseS := by ohyp
example : Thm natEnv [nat, nat, falseS] falseS := by ohyp
example : Thm natEnv (List.replicate 16 nat ++ [falseS]) falseS := by
  simp only [List.replicate, List.cons_append, List.nil_append]; ohyp
example : Thm natEnv [nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, falseS] falseS := by ohyp
example : Thm natEnv [nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, nat, falseS] falseS := by ohyp
example (Γ : List Lean4Lean.VExpr) : Thm natEnv (nat :: falseS :: Γ) falseS := by ohyp
example (h : Thm natEnv [nat, nat] falseS) : Thm natEnv [nat, nat] falseS := by
  fail_if_success ohyp
  first | ohyp | exact h
example (h : Thm natEnv [] falseS) : Thm natEnv [] falseS := by
  fail_if_success ohyp
  exact h
```

- Indices 0, 1, 2 (the reproducer), 16 (twice: literal and via
  `List.replicate`) and 20 succeed.
- The two no-match cases fail; the goal is then closed by `exact h` with no
  error logged, so the failed search leaves neither a partial proof nor
  deferred obligations.
- Before the change the same file reported `unsolved goals …
  ⊢ nat.lift.lift = ⊥ₒ` at the index-16 and index-20 lines, and
  `fail_if_success ohyp` reported that `ohyp` succeeded.

## Verification

- `nix develop -c lake build` passed (131 jobs) with the change; every module
  importing `Obj/Tactic` was rebuilt, so all existing uses of `ohyp` still
  elaborate.
- `nix develop -c lake env lean --trust=0` on an audit importing `Incomplete`:
  `incomplete_unconditional`, `incomplete_rosser`, `incomplete_rosser'`,
  `incomplete_of_wf`, `incomplete_of_wf'`, `second_incompleteness`,
  `second_incompleteness'`, `con_unprovable`, `bconsistent` and `bhaltsSound`
  each report exactly `[propext, Classical.choice, Quot.sound]`.
- `nix flake check` passed.
