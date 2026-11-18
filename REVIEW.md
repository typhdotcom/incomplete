State: COMPLETE
Turn: none
Candidate: rvpolkrnqyyyquwsznxyopkmuksuxlkl / 74c2107e89835d9c76795abb0fec7c68f7e948ca

# Consistent, ω-inconsistent context review

## Objective and meaning

Review the construction, over every consistent well-formed extension of
`natEnv`, of a consistent context that proves an existential statement while
refuting every numeral instance of its body. The context is `[Prov T falseS]`
for the actual arithmetized certificate checker, for every `TablesFor env T`.

The candidate adds `Incomplete/Obj/Omega.lean`, its library import, README
statements and definitions, and package version `0.5.0`, after the accepted
Löb development (`5853cb17`).

## Accepted foundation

- The formal judgment and upstream/fork dependencies remain as documented in
  `README.md`. These are results about that specification; they establish no
  kernel implementation correctness.
- Preserve the accepted Gödel–Kleene, Rosser, second incompleteness, Löb and
  bounded unconditional results. Their statements and axiom constraints are
  unchanged.
- `Prov T P` is the object proposition asserting an impredicatively encoded
  existential witness for `chkT T` accepting a certificate of `P`. It is
  distinct from the host predicate `Provable env P` and from the
  double-negation halting sentence.
- Löb assumes neither consistency nor halting soundness. This construction
  explicitly assumes `Consistent env`; it asserts a context over `env`, whose
  checker is unchanged, rather than constructing a new environment.
- The source and axiom constraints in `AGENTS.md` remain in force.

## Verdict

Accepted. No blocking finding was identified. The review is complete, and no
worker action remains.

Context consistency follows by discharging a hypothetical derivation of
`falseS` from `Prov T falseS`, applying Löb at `falseS`, and contradicting
base consistency. The existential statement is precisely the context's
hypothesis, a closed well-typed proposition.

For each host natural number `k`, base consistency and checker adequacy imply
that the checker returns a nonzero number on that certificate of `falseS`.
The internal numeral computation and successor disequality then prove the
negation of that numeral instance already in the empty context. Weakening
supplies it in the singleton context. The family of separate proofs is a
host quantification, not a proof of an object universal negation; no internal
witness extraction or soundness assumption is smuggled into the argument.

`omega_inconsistent_exists` discharges the table-existence obligation using
well-formedness. The README accurately describes the assumptions, the
context/environment distinction, and the checker predicate. The version and
library import match the new public results.

## Current drawers

None. D1 remains closed; the accepted hypothesis-search fix is unchanged.

## Verification

- `nix develop -c lake build` passed (133 jobs).
- Independently re-elaborated `Incomplete/Obj/Omega.lean` with
  `lake env lean --trust=0`; it passed without warnings.
- A separate `lake env lean --trust=0` audit passed for all fifteen README
  headline theorems and the three new supporting theorems
  `prov_false_ctx_consistent`, `prov_false_ctx_proves_prov`, and
  `not_prf_false_lit`. Each reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- Disposable probes checked the explicit hypotheses, closed proposition
  typing, the existential body's exact syntax, and substitution at every
  numeral against the refuted predicate. The combined theorem also checked
  in that explicit existential-and-instances formulation.
- Source inspection found no proof holes, native decision proofs, custom
  axiom declarations, or unsafe definitions in the new module.
- `nix flake check` passed. Existing warnings in unchanged modules remain
  nonblocking.
