State: READY FOR REVIEW
Turn: reviewer
Candidate: wssqvmlykpntlotqlutzskusotslnyow / 49771b318eb68ef97a2268a81389c755d14094af

# Whole-repository publication review

## Objective and meaning

Review version `0.12.1` before sharing it with the Lean community: do the
formal results establish the advertised claims, are their assumptions and
interpretations clear, and does the package work with its pinned dependencies?
The candidate is the entire repository. It is the returned candidate `0.12.0`
(`b567dcd48eb8`) plus the repairs for D2 and D3 below.

The review covers all 101 modules under `Incomplete/`, the root import file,
the public README, package configuration, development tasks, Nix checks, and
license. Mathematical inspection follows the definitions, theorem statements,
interfaces and load-bearing reductions. It reuses the preceding accepted
reviews for unchanged subsidiary arguments; it does not claim a new line-by-line
reading of every arithmetic proof.

## Accepted foundation

- The object theory is the pinned fork's formal `VEnv.HasType` /
  `VEnv.IsDefEq` judgment. The upstream/fork boundary is documented in
  [README.md](README.md#dependency). These results establish no kernel
  implementation correctness.
- Preserve the full-theory incompleteness, Löb, derivability and modal results,
  with the hypotheses recorded in [README.md](README.md#scope). Full-theory
  consistency and `HaltsSound` are not established here.
- Unconditional consistency and soundness concern `BProvable natEnv` and
  `BProvable clEnv`. `clEnv` adds the object axiom `dneS`; the bounded set
  model interprets it. Full and bounded provability must remain distinct.
- Chaitin complexity uses the numeric `PR.code` as description size and the
  first component of the least zero witness as output. The README explicitly
  defines this description system; no binary program-length or invariance
  theorem is claimed.
- Source and axiom constraints remain those of `AGENTS.md`. Dependency pins,
  toolchain and package version identify the candidate.
- Problems identified in this review are repair obligations. Do not accept
  the publication review while leaving them as optional polish or using a
  passing proof check to waive documentation or build-quality defects.

## Submission

Three commits on top of the returned candidate and its review record:

| Change / commit                 | Content                                                                                                                                               |
| ------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| `uwonowsutrlo` / `0c75e975a560` | D2: doc comments in `Final`, `Extend`, `Rosser`, `Second` (4 files, comments only).                                                                   |
| `mnspulvvvupp` / `cd34d17b4f6e` | D3, project: supported lemma names, unused simp arguments, bindings and section variables, removal of an existing linter suppression (41 Lean files). |
| `wssqvmlykpnt` / `49771b318eb6` | D3, dependency: lean4lean pin and manifest `b158604d…` → `db323b9f…`, README pin, version `0.12.0` → `0.12.1`.                                        |

No definition changed, and none of the 33 theorem statements displayed in
the README changed. Batteries (`v4.34.0`) and the toolchain
(`leanprover/lean4:v4.34.1`) are unchanged; `lake update lean4lean` moved only
the lean4lean entry of `lake-manifest.json`.

## Current drawers

### D2 — Theorem documentation reverses the halting interpretation

Status: resolved, awaiting review

Each corrected comment, against the statement it describes:

- `Final.lean:8–11` (module) and `Final.lean:24–26`
  (`incomplete_of_consistent`), `Extend.lean:214–216` (`incomplete_of_wf`):
  "does not prove the true non-halting sentence `notHalts d ⌜d⌝` of some
  machine `d` on its own number; if the theory's proofs of `halts` sentences
  are sound (`HaltsSound`), it does not refute it either." The conclusion is:

  ```lean
  ¬d.Halts d.code ∧ ¬Provable env (notHalts d d.code) ∧
    (HaltsSound env → ¬Provable env (halts d d.code))
  ```

  "Undecided" is gone: truth and unprovability need consistency only,
  irrefutability the additional hypothesis.

- `Rosser.lean:350–352` (`rosser_of_check`): "the non-halting sentence
  `notHalts d ⌜d⌝` of the Rosser machine `d` on its own number is a closed
  proposition, true of the machine, and neither provable nor refutable." The
  type gives `env.HasType 0 [] (notHalts d d.code) (.sort .zero)`,
  `¬d.Halts d.code`, `¬Provable env (notHalts d d.code)` and
  `¬Provable env (halts d d.code)`, from consistency. The former text said
  "false of the machine".

- `Rosser.lean:429–430` (`incomplete_rosser`): "neither proves nor refutes the
  true non-halting sentence of some machine on its own number"; same
  conclusion, no `HaltsSound`.

- `Second.lean:4–12` (module): titled "The second incompleteness theorem,
  reduced to its internal step"; `Con T` is "the non-halting sentence
  `notHalts (conM T) 0`"; it ends by pointing to `Obj/Second.lean`, which
  proves the internal step (`con_imp_G0_provable`) and the theorem
  (`con_unprovable`, `second_incompleteness`), replacing "that internal proof is
  not given here".

- `Second.lean:25` (`Con`): "**Consistency**, as a non-halting sentence: no
  certificate proves `False`", matching `Con T := notHalts (conM T) 0`, where
  `conM T` halts iff some certificate proves `falseS` (`con_true_iff`).

Search. All module docstrings, declaration docstrings, comments and the
README were searched for `halting sentence`, `non-halting`, `undecid`,
`independent`, `refut`, `irrefut`, `neither prov`, `false of` and
`true of`. The remaining uses are correct and unchanged:
`Sentences.lean:4,80` and `BSigma.lean:194` describe `halts` and its
Σ₁-completeness; `Obj/Loeb.lean:7` names the positive `haltsE` sentence;
`Obj/Loeb.lean:438`, `Obj/SolovayLemmas.lean:423`, `Main.lean:27–29`,
`README.md:413,590` concern `halts`; `Unconditional.lean:12,64` say neither
provable nor refutable for `incomplete_unconditional`, whose hypotheses are
all discharged; `README.md:44–45,101–105` already distinguish the
`HaltsSound` case; `Main.lean:9–12` and `Kleene.lean:4–8` already
separate unprovability from irrefutability under halting soundness.

### D3 — The supported build emits 307 Lean warnings

Status: resolved, awaiting review

Project (`mnspulvvvupp`):

- Deprecated names replaced by those the deprecation messages name, with
  identical signatures in the v4.34.1 core: `if_pos` → `ite_eq_left`,
  `if_neg` → `ite_eq_right`, `if_true` → `ite_true`, `if_false` →
  `ite_false`, `dif_pos` → `dite_eq_left`, `dif_neg` → `dite_eq_right` (224
  occurrences). No proof needed repair.
- Unused simp arguments removed in `Encode`, `LevelPR`, `BArith` (2),
  `Rules2` (3), `Obj/Iota`, `ListPR`, `CheckPR` (3), `Extend`, `EqEnv`,
  `Obj/BChecker` (4, one call) and `Obj/SolovayStep` (2).
- Unused section variables: `omit E in` for `Tms.mem`, `Tms.append`,
  `Tms.reverse` (`Obj/Chain`), `props_cons`, `props_map`
  (`Obj/SolovayStep`) and `Thm.cast` (`Obj/Core`). `Obj/Core.lean` carried
  `set_option linter.unusedSectionVars false`, which hid the `Thm.cast`
  warning; it is removed.
- Unused variables: the internal lemma `ZF.pi_eq_single_empty` (no uses)
  loses its unused hypothesis `h`; `ZF.num_inj`'s last pattern no longer names
  `m`, `n`; in `Encode.decCert` the `dite` binder is anonymous
  (`if _ : n % 16 = 0`) and its `decreasing_by` refers to the hypothesis as
  `‹¬n % 16 = 0›`. The definition remains a `dite`.

Imported theory: the fork commit
[`db323b9f1770`](https://github.com/typhdotcom/lean4lean/commit/db323b9f1770df1bd15c54b01b10eb85a7b0962b)
("Build the imported theory without warnings on Lean v4.34") repairs the 35
deprecations in `Theory/VExpr.lean` and the two warnings in
`Theory/Typing/Projection.lean` (an anonymous binder for the unused hypothesis
of `FieldsWF.keptTele`, one simp argument removed), without changing theorem
statements. `lakefile.toml` and `lake-manifest.json` pin it together.

The project's source contains no `set_option linter…`, `nolint`, or
warning flags; `lakefile.toml` sets no options.

Closure evidence, on the committed candidate with a clean working copy:

| Build                                                                | Compiled                                     | Warnings                                      |
| -------------------------------------------------------------------- | -------------------------------------------- | --------------------------------------------- |
| Returned candidate, `rm -rf .lake/build`                             | 102 `Incomplete` modules; lean4lean replayed | 307 (270 project in 40 modules, 37 lean4lean) |
| Candidate, `rm -rf .lake/build .lake/packages/lean4lean/.lake/build` | 102 `Incomplete` and 24 `Lean4Lean` modules  | 0                                             |
| Candidate, ordinary `nix develop -c lake build` afterwards           | up to date, 153 jobs                         | 0                                             |

Counts are `warning` lines in the captured logs. Per-module counts before
the repair: AndEnv 2, BArith 2, CertNat 1, CertPR 4, CheckPR 5, ClEnv 3,
Encode 32, EqEnv 3, Extend 4, InstPR 8, LeafPR 3, LevelPR 5, LiftPR 12,
ListPR 2, Modal/Complete 2, Modal/Letterless 1, Model 1, ModelSound 16,
NatEnv 2, Obj/BChecker 5, Obj/Certs 1, Obj/Chain 2, Obj/Chaitin 2,
Obj/Graph 2, Obj/Holes 51, Obj/Iota 1, Obj/Numeral 1, Obj/Ring 1,
Obj/Sigma 12, Obj/SolovayCode 5, Obj/Solovay 3, Obj/SolovayStep 4,
Obj/Template 6, PRLib 6, ProjRules 23, Rosser 2, Rules2 4, Rules3 9,
SubstPR 17, ZF 5; after, 0 in each.

## Closed drawers

D1 remains closed: hypothesis search passes at indices 0, 1, 2, 16 and
32, and an unsuccessful search permits a fallback proof without a partial
proof or deferred errors. As in the accepted correction, search covers the
explicit context prefix; computed `List.replicate` contexts are normalized
before these probes.

## Verification

Run on the candidate after the dependency update and the fresh build above.

- `nix develop -c lake build` passed: 153 jobs, 0 warnings.
- The README's 48 `#print axioms` commands, checked with
  `nix develop -c lake env lean --trust=0`: every result is exactly
  `[propext, Classical.choice, Quot.sound]`.
- The whole-namespace audit below, with `--trust=0`: "Audited 4048 Incomplete
  theorems; all axiom dependencies are allowed."
- README statement conformance: each of the 33 displayed `theorem` statements
  was quantified over its binders, elaborated after opening `Incomplete`,
  `Lean4Lean`, `Incomplete.Obj` and `Incomplete.Modal`, and checked
  definitionally equal to the type of the named constant (`isDefEq`, `--trust=0`): 33 of 33 pass.
- Source scan: no `sorry`, `admit`, `native_decide`, axiom declarations,
  `unsafe`, `extern`, `implemented_by`, or linter options in the project Lean
  sources.
- `nix flake check` passed: formatting, statix, deadnix, gitleaks, shellcheck,
  actionlint and markers.

The previous reviewer's inspection record for `0.12.0` (abridged), which these repairs
leave in force apart from D2 and D3:

| Area                                               | Surface reviewed                                                                                         | Evidence and conclusion                                                                                                                                                                                                                                                                                                                                                                                    |
| -------------------------------------------------- | -------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Package and public surface                         | `Incomplete.lean`, README, Lake manifest/configuration, toolchain, Nix modules, `tasks.nu`, license      | All 101 modules are reachable from `import Incomplete`, and each has a module docstring. Installed dependency HEADs match the manifest. The fork pin and Lean/Batteries versions match the README. Apache 2.0 matches the dependency. All 33 displayed theorem statements conform to the exported types.                                                                                                   |
| Formal judgment and environments                   | Pinned `Theory.Typing.Basic` / `Env`; `NatEnv`, `NatWF`, `NatDeclWF`, `Extend`, `EqEnv`, `AndEnv`        | The target is the actual inductive judgment, including all three projection rules. `natEnv` is identified with `addInduct natDecl`; declaration and generated-rule well-formedness are proved. Every finite well-formed environment supplies tables, including inductive blocks, quotients and mutual definitions.                                                                                         |
| Machines and representability                      | `PR`, `PRLib`, `Arith`, `Adequacy`, `Sentences`                                                          | Checked valuation order, primitive recursion, compilation, numeral adequacy, `PR.code`, and the definitions of halting/non-halting and provability. `halts` is the negation of `notHalts`; it is not silently identified with a positive existential inside the intuitionistic object theory.                                                                                                              |
| Encoding and full proof checker                    | `Encode`, `Cert*`, `Check*`, `*PR`, `Rules2`, `Rules3`, `ProjRules`, `Enumerate`, `Diag`                 | Numbering round trips, certificate soundness/completeness, numeric conclusion checks and PR computation connect actual derivations to the diagonal machine. Projection conditions are checked at closed levels. No assumed effective checker is left in the public full-theory wrappers.                                                                                                                   |
| Bounded judgment and model                         | `Bounded`, `BArith`, `BSigma`, `LeafPR`, `ZF`, `ZFUniv`, `Model`, `ModelSound`, `Unconditional`, `ClEnv` | `BDefEq` embeds into full typing; certificates enforce its bounds and exclude projection rules. Sets are constructed as a quotient of well-founded trees. Proof irrelevance and impredicative products are modeled; `BDefEq.sound` yields consistency and halting soundness. A probe proves that a higher sort is inhabited in full typing but uninhabited in the bounded judgment.                        |
| Object language, arithmetic and proof manipulation | `Obj/Typing` … `Obj/Sigma`                                                                               | `ObjEnv`'s rules and adequacy are discharged for full and bounded typing. `Thm` is existence of an actual typed proof. Checked capture-sensitive template interfaces, closed/numeral certificate construction, internal modus ponens and graph completeness through `ok_exists`. Tactic probes exercise hypothesis search, failed-search recovery and symbolic semiring reasoning in the bounded judgment. |
| First and second incompleteness                    | `Kleene`, `Main`, `Final`, `Induct`, `Rosser`, `Second`, `Obj/Reduce`, `Obj/Second`                      | The diagonal argument uses proved representability and checking. Rosser's finite prefix and inductive tail remove the halting-soundness premise. `con_true_iff` identifies the actual checker's non-halting interpretation with consistency; `sigma_dg` and `con_imp_G0_provable` discharge the internal step of the second theorem. The public hypotheses match the README.                               |
| Löb, derivability and arithmetic GL soundness      | `Obj/Checker`, `BChecker`, `Loeb`, `Omega`, `Derivability`, `GL`                                         | Checked `Prov`/`ProvC`, the Löb machine, internal certificate transformations, D1–D3, formalized Löb and full/bounded checker instances. `IsChecker` alone does not supply external soundness: the completeness wrappers separately discharge it. Classical GL uses `dneS`; `iGL` and FairBot retain their documented weaker assumptions.                                                                  |
| Kripke and arithmetical completeness               | `Modal/*`; `Obj/SolovayCode`, `SolovayStep`, `SolovayLemmas`, `Solovay`                                  | Necessitation applies to theorems, not local modal assumptions. The finite countermodel is nonempty, transitive and irreflexive. Solovay's truth lemma and `no_refuted` connect the actual checker and halting soundness to the finite walk; the public and bounded wrappers discharge the generic premises.                                                                                               |
| Letterless results and classical fragment          | `Modal/Letterless`, `Obj/Letterless`, `BProvLogic`                                                       | Height includes realization of every smaller level; stabilization is from box depth onward. `dec` checks every level through that depth, whereas `lim` records eventual truth. `BProv` refers to the fragment's checker, so unconditional GL completeness does not presume full-theory consistency.                                                                                                        |
| Chaitin                                            | `Obj/Chaitin`, `Chaitin`                                                                                 | Least-zero output is functional. Counting uses at most `L + 1` indices, and eventual complexity is proved separately. `chaitin_core` uses a sound and complete checker plus consistency, without halting soundness.                                                                                                                                                                                        |

The whole-namespace audit can be rerun in a temporary Lean file with
`nix develop -c lake env lean --trust=0 <file>`:

```lean
import Incomplete
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Incomplete).isPrefixOf name && info.isTheorem then
      let axs ← collectAxioms name
      for ax in axs do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      count := count + 1
  logInfo m!"Audited {count} Incomplete theorems; all axiom dependencies are allowed."
```

The statement-conformance check uses this command, one line per displayed
theorem, e.g. `conform loeb : ∀ (env : VEnv) (hwf : env.WF) …, Provable env P`:

```lean
open Lean Elab Command Term Meta in
elab "conform " n:ident " : " t:term : command => liftTermElabM do
  let ty ← elabType t
  Term.synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars ty
  let c ← getConstInfo (← realizeGlobalConstNoOverload n)
  let cty ← instantiateTypeLevelParams c.toConstantVal (← mkFreshLevelMVarsFor c)
  unless ← isDefEq ty cty do throwError m!"{n}: {ty} vs {cty}"
  logInfo m!"ok {n}"
```

## Worker completion requirement

Work from this `REVIEW.md`, resolve open drawers, and rewrite this file as
the next `READY FOR REVIEW` submission. Supply exact evidence for each drawer
and identify the finalized candidate as `change / commit`. Follow
`AGENTS.md`: update stale README/version information, run the required Lean
verification and `nix flake check`, commit the candidate, then record its
identity and commit the review submission. Merely replying in chat is not a
submission.
