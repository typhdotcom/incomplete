State: COMPLETE
Turn: none
Candidate: lxooslookymonlxxvnszqkrtovltqyvz / c329860a229a0adbdd215b767bd7035bb1ada0c4

# Löb review

## Objective and meaning

Review Löb's theorem for the actual arithmetized certificate checker: every
closed proposition `P` of a well-formed extension of `natEnv` is provable if
the theory proves `Prov T P → P`, for every `TablesFor env T`. Review the
supporting generalizations of internal completeness and modus ponens, the
halting-form variant, and the consistency corollary.

The implementation under review is the two commits after `dc449884`, including
`Incomplete/Obj/Loeb.lean`, changes in `Obj/Second.lean` and `Obj/Reduce.lean`,
the library import, version `0.4.0`, and the README additions.

## Accepted foundation

- The formal judgment and upstream/fork dependencies remain as documented in
  `README.md`. These are results about that specification; they establish no
  kernel implementation correctness.
- Preserve the accepted Gödel–Kleene, Rosser, second incompleteness and bounded
  unconditional results. Their statements and axiom constraints are unchanged.
- `Prov T P` is the object proposition asserting an impredicatively encoded
  existential witness for `chkT T` accepting a certificate of `P`. It is
  distinct from the host predicate `Provable env P` and from the
  double-negation halting sentence.
- Löb's theorem assumes neither `Consistent env` nor `HaltsSound env`.
  `prov_lit_iff` has its documented consistency assumption; `prov_sound` has
  its documented halting-soundness assumption.
- The source and axiom constraints in `AGENTS.md` remain in force.

## Verdict

Accepted. No blocking finding was identified. The review is complete, and no
worker action remains.

The proof establishes the advertised Löb rule for every closed proposition,
with all machine and internal-completeness hypotheses discharged. Inspection
followed the positive halting sentence, its syntax encoding, the self-reference
identity `fn_loebM_code`, the proved graph lemma in `sigma_E`, internal
certificate modus ponens, and `loeb_core`. The final step obtains an actual
closed certificate of the internally proved implication and constructs its
positive halting witness. It does not extract an external witness from an
arbitrary proof of an existential sentence.

The generalized `sigma_of_fin` retains its graph and closed-conclusion
premises; `sigma_E` discharges them for positive halting. The original
`sigma_of` remains a specialization, and the existing second theorem builds
and retains its previous axiom dependencies. The halting-form Löb variant
uses the proved implication from positive provability, and the consistency
corollary specializes Löb to `falseS`.

The accompanying README correction removes a stale claim that `HaltsSound`
is used only by the Gödel–Kleene form: `prov_sound` now uses it too.

## Current drawers

None. D1, closed in the preceding review, remains closed; hypothesis-search
implementation was not changed in this candidate.

## Verification

- `nix develop -c lake build` passed (132 jobs).
- A fresh temporary package containing all project sources and the pinned
  package configuration built successfully (132 jobs), recompiling every
  project module and reusing installed dependency artifacts.
- An independent `lake env lean --trust=0` audit passed for all thirteen
  README theorems, including `loeb`, `loeb_halts` and
  `con_unprovable_of_loeb`. Additional audits covered `prov_of_provable`,
  `prov_lit_iff`, `prov_sound`, `con_iff_not_prov`, `Obj.sigma_E`,
  `Obj.sigma_of_fin` and `Obj.prf_mpT`. Every audited result reports exactly
  `[propext, Classical.choice, Quot.sound]`.
- Inspected the fully explicit types of the headline and internal theorems.
  Disposable specializations checked reflection at `falseS` and the
  unprovability of reflection for an unprovable proposition.
- Source inspection found no new proof holes, native decision proofs, custom
  axiom declarations, or unsafe definitions in the changed Lean files.
- `nix flake check` passed. Existing unused-variable and unused-simp-argument
  warnings remain nonblocking.
