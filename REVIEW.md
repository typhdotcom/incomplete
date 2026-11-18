State: COMPLETE
Turn: none
Candidate: yvnpokxyustvvsttkxvlmvwnspyllrwz / 7e6276a9902567f6f02fbd55586212322cfbe4d6

# Rosser and second incompleteness review

## Objective and meaning

Review the Rosser and second incompleteness developments and their object-level
proof toolkit, including the correction to hypothesis search returned as D1.

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

## Verdict

Accepted. D1 is closed, and the review is complete. No worker action remains.

The headline theorems and their documented hypotheses passed the preceding
mathematical review at `a9192d26a3bd`. The current candidate changes only the
`ohyp` elaborator; it corrects the returned failure without changing the
formal definitions or theorem statements. The existing proof evidence remains
applicable, and the corrected tactic passed independent regression checks.

## Closed drawers

### D1 — `ohyp` stops before reaching a matching hypothesis

Status: closed

The original context `[nat, nat, falseS]` now succeeds with `ohyp`. Candidate
lookup is performed as a tactic sequence under `withoutRecover`, with `done`
requiring completion and saved-state restoration on failure. Search traverses
the explicit context prefix up to reducible unfolding, replacing the fixed
16-entry limit. An open tail is searched through its explicit prefix.

Independent checks passed for indices 0, 1, 2, 3, 7, 15, 16, 17, 20, 31 and
32, an explicit prefix over a variable context tail, and the submitted
normalized `List.replicate` case. Empty and nonempty no-match contexts failed
as expected, then allowed a fallback proof with no logged elaboration errors.
An additional two-goal probe confirmed that a failed search preserves the
remaining goals. Every success case exercised `ohyp` itself.

## Verification

- `nix develop -c lake build` passed (131 jobs). The fresh project build and
  mathematical inspection from the preceding review are reused for the
  unchanged formal development.
- An independent temporary probe, run with
  `nix develop -c lake env lean --trust=0`, passed the submitted regression
  cases and the additional cases above.
- The same audit checked all ten README theorems:
  `incomplete_unconditional`, `incomplete_rosser`, `incomplete_rosser'`,
  `incomplete_of_wf`, `incomplete_of_wf'`, `second_incompleteness`,
  `second_incompleteness'`, `con_unprovable`, `bconsistent` and `bhaltsSound`.
  Each reports exactly `[propext, Classical.choice, Quot.sound]`.
- `nix flake check` passed for the review submission. Existing unused-variable
  and unused-simp-argument warnings remain nonblocking.
