State: RETURNED
Turn: worker
Candidate: wvyqrvqrxptmnnkxvrrqyzyqopxtpvsw / a9192d26a3bd47573d9a3f67fcb217e0511df091

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

## Verdict

Returned for D1. The formal headline results passed the build, axiom audit,
and statement/dependency inspection. The new exported `ohyp` tactic fails a
routine valid context despite advertising hypothesis search; this behavior
needs correction before accepting the submitted toolkit.

## Current drawers

### D1 — P2: `ohyp` stops before reaching a matching hypothesis

Status: open

`Incomplete/Obj/Tactic.lean:67–75` returns after `evalTactic` accepts an
attempt, without ensuring that its deferred elaboration obligations succeed.
The following ordinary context reproduces the failure:

```lean
import Incomplete
open Incomplete Incomplete.Obj

example : Thm natEnv [nat, nat, falseS] falseS := by
  ohyp
```

Lean exits with an unsolved goal `nat.lift.lift = falseS`. The same judgment
passes with `exact Thm.hyp (i := 2) (by olookup)`. Targets at indices 0 and 1
also pass with `ohyp`; the sweep of contexts
`List.replicate n nat ++ [falseS]` fails for every tested `n` in `2…16`.
The explicit-index controls establish that these are valid judgments.

The separate `List.range 16` cutoff also excludes valid hypotheses at index
16 and beyond; explicit lookup at index 16 passes. Repair hypothesis search
so an unsuccessful candidate is fully rejected before moving on, and search
the available context rather than imposing that undocumented fixed limit.
Keep the fix confined to hypothesis search and its verification.

Closure evidence: small regression checks for successful lookup at indices
0, 1, 2 and 16, including the reproducer above; a no-match case that fails
without leaving a partial proof or deferred obligations; the library build;
and the public theorem axiom audit. Exercise `ohyp` itself in these checks,
rather than substituting explicit lookup.

## Verification

- `nix develop -c lake build` passed (131 jobs).
- A fresh temporary copy of all project Lean sources and package
  configuration built successfully (131 jobs), recompiling every project
  module and reusing the installed dependency artifacts.
- `nix develop -c lake env lean --trust=0` on an audit importing `Incomplete`
  passed. All ten README theorems report exactly
  `[propext, Classical.choice, Quot.sound]`: `incomplete_unconditional`,
  `incomplete_rosser`, `incomplete_rosser'`, `incomplete_of_wf`,
  `incomplete_of_wf'`, `second_incompleteness`, `second_incompleteness'`,
  `con_unprovable`, `bconsistent`, and `bhaltsSound`. The same audit passed
  for `con_imp_G0_provable`, `sigma_dg`, and `Obj.ok_exists`.
- Inspected the definitions of `ObjEnv`, `Thm`, object equality, symbolic
  evaluation, proof and certificate predicates, templates, and consistency.
  Traced Rosser's finite-prefix/tail induction and the second theorem's
  internal graph certificates, instantiation, modus ponens, `sigma_dg`, and
  `Con T → G0 T`. The headline statements have the documented hypotheses;
  the internal implication is proved rather than assumed. The base
  certificate premises of `Obj.ok_exists` are discharged in `sigma_of`.
- Source inspection found no proof holes, native decision proofs, or added
  axiom declarations. The new partial definitions are elaborator helpers.
- `nix flake check` passed for the candidate. Existing unused-variable and
  unused-simp-argument warnings remain nonblocking.
- The isolated D1 reproducer failed; its explicit-index controls passed.

## Worker completion requirement

Work from this `REVIEW.md`, resolve D1, and rewrite this file as the next
`READY FOR REVIEW` submission with the exact finalized candidate identity
and evidence for the drawer. Follow `AGENTS.md`: run the relevant Lean
checks and `nix flake check`, commit the candidate, then record its identity
and commit the review submission. Merely replying in chat is not a
submission.
