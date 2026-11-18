State: COMPLETE
Turn: none
Candidate: lkmszzkpkzuwknksqmqkxrzvzqqlzosn / 9deb50bc684448f50b72689a073c74a4b3f59bb1

# Classical bounded provability-logic review

## Objective and meaning

Review the unconditional identification of GL with the provability logic of
the projection-free `Prop`/`Type` fragment of `clEnv`, the extension of
`natEnv` by a DNE constant. Verify the fragment's set-model consistency and
halting soundness, its actual bounded checker, the generalization of the proof
kit and checker-dependent arguments, and the letterless corollaries.

The candidate is the development after `6cf13244`, ending at version
`0.10.0`. It adds `ClEnv`, `BProvLogic`, `Obj/Typing`, `Obj/Leaf`, `Obj/Checker`
and `Obj/BChecker`, generalizes the object-level modules, and extends the set
model's environment interface.

## Accepted foundation

- The formal judgment and upstream/fork dependencies remain as documented in
  `README.md`. These results establish no kernel implementation correctness.
- Preserve the accepted incompleteness, bounded-model, Löb, derivability,
  FairBot, finite Kripke, Solovay and letterless results. The full-theory
  headline statements retain their original hypotheses and actual typing
  judgment, through specializations of the generalized development.
- `BDefEq` and `BProvable` remain the original bounded judgment and its closed
  theoremhood predicate. The new abstract interface does not redefine them.
- `clEnv` contains an object-theory axiom constant for DNE. Its interpretation
  is proved valid in the set model; no new Lean axiom is introduced.
- The unconditional result concerns bounded theoremhood with `BProv` read
  through `bchkT clT`. It does not prove consistency or halting soundness of
  the full typing judgment of `clEnv`.
- The source and axiom constraints in `AGENTS.md` remain in force.

## Verdict

Accepted. No blocking proof or implementation finding was identified. The
review is complete, and no worker action remains for this milestone.

`Typing` keeps the underlying environment and chosen equality judgment
separate. `ObjEnv` supplies the actual inference rules, substitution,
weakening and primitive-recursive adequacy needed by the proof kit. Its
bounded instance is proved directly from `BDefEq`; the map to full typing
supports syntactic closure arguments without replacing bounded derivations
by full ones. Iota is derived from the available equality rules in the chosen
judgment.

`IsChecker` packages internal closed certificates, modus ponens and numeral
instantiation. These properties support the generalized derivability and Löb
arguments. Generic Solovay completeness additionally requires external
checker soundness and halting soundness; these remain explicit premises of
the generic result, rather than being inferred from internal closure alone.

The bounded checker conjoins the full certificate check with the original
leaf-bound check. Its external soundness and completeness use the existing
certificate correspondence for `BDefEq`. Internal bounds are preserved by
application certificates, modus ponens and numeral certificates, establishing
the bounded `IsChecker` instance used in the new result.

The set-model extension permits only the original constants or monomorphic
constants with a proved interpretation in their types, and only the original
extra equality rules. The new DNE constant has such an interpretation.
`clEnv` is well formed, extends `natEnv`, has the stated concrete tables, and
has a bounded DNE proof. Model soundness then discharges bounded consistency
and halting soundness. The new public GL completeness theorem has no residual
model, checker, soundness, DNE or abstract-judgment assumptions. Its realizations
are propositions of the bounded fragment and its boxes use that fragment's
checker. The letterless consequences use this theorem and the accepted level
classification.

One README wording ambiguity was corrected during review: the downward
consistency implications are true and unprovable *for every n*, rather than
*at every level*. Their tower evaluations fail at one finite level, so the
previous wording obscured the accepted truth/provability distinction. No Lean
implementation changes were made by the reviewer.

## Current drawers

None. D1 remains closed; hypothesis search was not changed in this round.

## Verification

- `nix develop -c lake build` passed (151 jobs).
- A fresh temporary package containing every project source and the pinned
  package configuration built successfully (151 jobs), recompiling project
  modules while reusing only installed dependency artifacts.
- Independent `lake env lean --trust=0` audits passed against both the working
  package and freshly rebuilt artifacts. All 46 README headline theorems
  report exactly `[propext, Classical.choice, Quot.sound]`. Additional audits
  of the concrete DNE proof, bounded checker instance and adequacy, bounded
  judgment instance, generic model soundness, and new GL soundness and
  completeness report subsets of that set.
- Inspected explicit theorem types: unconditional bounded GL results have
  no residual theory assumptions, and the full-theory Löb and Solovay public
  statements retain their original hypotheses and typing judgment.
- Disposable probes checked exact bounded-checker adequacy for every sentence,
  existence of an accepted DNE certificate, and rejection of every certificate
  of bottom. A valid full sort certificate for `Type : Type 1` fails the leaf
  check and is rejected by `bchkNum`; the set model independently rules out
  the corresponding bounded judgment.
- Probes checked the exact bounded box translation, compatibility of full
  and generic realizations, an unconditional bounded counter-realization of
  reflection, a bounded proof from a positive letterless decision, and
  unconditional true-but-unprovable consistency iterations.
- Source inspection found no proof holes, native decision proofs, custom Lean
  axiom declarations, or unsafe definitions in project sources.
- `nix flake check` passed. Unused-section-variable and unused-simp-argument
  warnings remain nonblocking. Temporary probes and the fresh package were
  removed after verification.
