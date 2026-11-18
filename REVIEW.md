State: COMPLETE
Turn: none
Candidate: ymkzmtqqllvswpulyxzulsynptxtyowy / 452a6c3140ca3bff8fcfeab52b382209f9c0e731

# Letterless-fragment review

## Objective and meaning

Review the classification and finite decision of letterless GL formulas by a
level tower, the height lemma for finite Kripke models, and the corresponding
object-theory provability and truth results. Review the true-but-unprovable
iterated-consistency examples and the separation from the intuitionistic
fragment.

The candidate comprises the three commits after `5bb1ee99`, adding
`Modal/Letterless.lean`, `Obj/Letterless.lean`, their public imports, README
statements and version `0.9.0`.

## Accepted foundation

- The formal judgment and upstream/fork dependencies remain as documented in
  `README.md`. These results establish no kernel implementation correctness.
- Preserve all accepted incompleteness, bounded-model, Löb, derivability,
  FairBot, finite Kripke and Solovay results. Their sources and statements are
  unchanged in this candidate.
- `Prov T P` is the actual certificate-checker proposition, tied to the formal
  typing judgment by `TablesFor env T`. Host provability remains distinct
  from this object sentence.
- The full object theory's halting soundness and proof of `dneS` remain
  explicit assumptions where used; they are not proved here. The source and
  axiom constraints in `AGENTS.md` remain in force.

## Verdict

Accepted. No blocking finding was identified. This review is complete, and
no worker action remains for the submitted milestone.

`Letterless` excludes every occurrence of a variable. The level evaluator
uses classical implication and boxes ranging over all smaller levels.
Stabilization at box depth follows structurally, and checking levels through
that depth includes the eventual value. The public decision theorem retains
its letterless premise; assigning all variables false does not decide GL for
arbitrary formulas.

The height interface requires both decrease along accessibility and a
successor at every smaller height. Finite transitive irreflexive models
satisfy both properties with longest-chain height. These conditions justify
both box directions of the height lemma, including branching frames. Chains
realize every height, so finite completeness yields the all-level criterion
and the Boolean decision theorem.

Realization independence holds even for arbitrary, untyped variable
assignments because letterless formulas never use them. Provability follows
from all levels using accepted GL soundness and `dneS`; the converse uses
Solovay and the documented halting-soundness premise. The truth predicate is
defined recursively with boxes read as host provability of the body's closed
realization. Structural induction identifies this predicate with the
eventual value; the proof does not assert a semantic model of arbitrary
object-theory sentences.

Halting soundness implies consistency by excluding a halting proof for a
constant nonzero machine. Repeated provability soundness then excludes every
`boxBot n`. Löb excludes each downward implication between consecutive
iterations, while its truth is vacuous because the preceding iteration is
unprovable. These results need no object DNE premise. The base case is proved
equivalent to `Con T`, whose unprovability needs only consistency. The
three-element algebra validates all intuitionistic calculus rules and refutes
the letterless DNE instance; the README correctly limits its claim to the
failure of removing DNE via that fragment.

The README, version and imports match these results and their assumptions.

## Current drawers

None. D1 remains closed; the accepted hypothesis-search fix is unchanged.

## Verification

- `nix develop -c lake build` passed (145 jobs).
- Independently re-elaborated both new modules with
  `lake env lean --trust=0`; both passed without warnings.
- A separate audit passed for all 38 README headline theorems. Each reports
  exactly `[propext, Classical.choice, Quot.sound]`. Additional audits covered
  stabilization, the finite height interface, algebra soundness, realization
  independence, halting soundness implying consistency, and the weaker
  one-direction and consistency corollaries; their dependencies are subsets
  of that set. Explicit public types confirm the documented assumptions.
- Disposable probes computed the heights of a branching frame with an extra
  terminal successor and checked its equivalence with a chain at the same
  height for every letterless formula.
- Boundary probes checked the exact level values of `boxBot 3`, the false
  level of `boxBot 3 → boxBot 2`, its true eventual value and false decision,
  the provable upward implication, and stabilization far beyond box depth.
- A concrete countermodel showed that `dec (neg (var 0)) = true` does not imply
  GL derivability, testing the need for the letterless guard. Object-theory
  specializations checked independence from an untyped variable assignment,
  the DNE-only provability direction, and a true-but-unprovable downward
  implication under halting soundness alone. A definitional probe checked
  the intended provability reading of nested boxes in `Modal.tr`.
- Source inspection found no proof holes, native decision proofs, custom
  axiom declarations, or unsafe definitions in the new modules.
- `nix flake check` passed. Existing warnings in unchanged modules remain
  nonblocking. Disposable probes were removed after use.
