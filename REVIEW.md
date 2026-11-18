State: RETURNED
Turn: worker
Candidate: qkxrkslrkqpoqqrtwywxnuylnpouyuon / b567dcd48eb8ca09fde9d26bfd0dd3baed7230e8

# Whole-repository publication review

## Objective and meaning

Review version `0.12.0` before sharing it with the Lean community: do the
formal results establish the advertised claims, are their assumptions and
interpretations clear, and does the package work with its pinned dependencies?
The candidate is the entire repository, including the Lean/dependency upgrade
after the preceding Chaitin review.

The review covers all 101 modules under `Incomplete/`, the root import file,
the public README, package configuration, development tasks, Nix checks, and
license. Mathematical inspection follows the definitions, theorem statements,
interfaces and load-bearing reductions below. It reuses the preceding accepted
reviews for unchanged subsidiary arguments; it does not claim a new line-by-line
reading of every arithmetic proof. Every project module was freshly elaborated.

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
  toolchain and package version identify the candidate. Change a dependency
  pin when required to repair the imported fork, following `AGENTS.md`.
- Problems identified in this review are repair obligations. Do not accept
  the publication review while leaving them as optional polish or using a
  passing proof check to waive documentation or build-quality defects.

## Verdict

Returned for D2 and D3. The formal verification below remains valid for the
candidate, but the publication review is not complete: misleading theorem
documentation and the build's warning backlog require repair. The previous
acceptance verdict is withdrawn.

## Review progress and evidence

The table records completed inspection and evidence, not acceptance of areas
with outstanding findings. D2 and D3 own the remaining work. Successful
elaboration validates the formal statements; inspection connects those
statements to the public claims; probes discriminate specific boundaries and
tactic behavior.

| Area | Surface reviewed | Evidence and conclusion |
| --- | --- | --- |
| Package and public surface | `Incomplete.lean`, README, Lake manifest/configuration, toolchain, Nix modules, `tasks.nu`, license | All 101 modules are reachable from `import Incomplete`, and each has a module docstring. Installed dependency HEADs match the manifest. The fork pin and Lean/Batteries versions match the README. Apache 2.0 matches the dependency. All 33 displayed theorem statements conform to the exported types. |
| Formal judgment and environments | Pinned `Theory.Typing.Basic` / `Env`; `NatEnv`, `NatWF`, `NatDeclWF`, `Extend`, `EqEnv`, `AndEnv` | The target is the actual inductive judgment, including all three projection rules. `natEnv` is identified with `addInduct natDecl`; declaration and generated-rule well-formedness are proved. Every finite well-formed environment supplies tables, including inductive blocks, quotients and mutual definitions. |
| Machines and representability | `PR`, `PRLib`, `Arith`, `Adequacy`, `Sentences` | Checked valuation order, primitive recursion, compilation, numeral adequacy, `PR.code`, and the definitions of halting/non-halting and provability. `halts` is the negation of `notHalts`; it is not silently identified with a positive existential inside the intuitionistic object theory. |
| Encoding and full proof checker | `Encode`, `Cert*`, `Check*`, `*PR`, `Rules2`, `Rules3`, `ProjRules`, `Enumerate`, `Diag` | Numbering round trips, certificate soundness/completeness, numeric conclusion checks and PR computation connect actual derivations to the diagonal machine. Projection conditions are checked at closed levels. No assumed effective checker is left in the public full-theory wrappers. |
| Bounded judgment and model | `Bounded`, `BArith`, `BSigma`, `LeafPR`, `ZF`, `ZFUniv`, `Model`, `ModelSound`, `Unconditional`, `ClEnv` | `BDefEq` embeds into full typing; certificates enforce its bounds and exclude projection rules. Sets are constructed as a quotient of well-founded trees. Proof irrelevance and impredicative products are modeled; `BDefEq.sound` yields consistency and halting soundness. A probe proves that a higher sort is inhabited in full typing but uninhabited in the bounded judgment. |
| Object language, arithmetic and proof manipulation | `Obj/Typing`, `Core`, `Attr`, `Tactic`, `Iota`, `Logic`, `Rec`, `Arith`, `Code`, `Eval`, `Bnd`, `Codes`, `Order`, `Closed`, `Ring`, `Ineq`, `Pair`, `DivMod`, `Strong`, `Cases`, `Cov`, `Reads`, `Key`, `Lift`, `Inst`, `Numeral`, `Fields`, `Check`, `Certs`, `Free`, `NumCert`, `Template`, `Holes`, `Chain`, `Leaf`, `Graph`, `Sigma` | `ObjEnv`'s rules and adequacy are discharged for full and bounded typing. `Thm` is existence of an actual typed proof. Checked capture-sensitive template interfaces, closed/numeral certificate construction, internal modus ponens and graph completeness through `ok_exists`. The recent generic evaluation lemmas retain the old conclusions. Tactic probes exercise hypothesis search, failed-search recovery and symbolic semiring reasoning in the bounded judgment. |
| First and second incompleteness | `Kleene`, `Main`, `Final`, `Induct`, `Rosser`, `Second`, `Obj/Reduce`, `Obj/Second` | The diagonal argument uses proved representability and checking. Rosser's finite prefix and inductive tail remove the halting-soundness premise. `con_true_iff` identifies the actual checker's non-halting interpretation with consistency; `sigma_dg` and `con_imp_G0_provable` discharge the internal step of the second theorem. The public hypotheses match the README. |
| Löb, derivability and arithmetic GL soundness | `Obj/Checker`, `BChecker`, `Loeb`, `Omega`, `Derivability`, `GL` | Checked `Prov`/`ProvC`, the Löb machine, internal certificate transformations, D1–D3, formalized Löb and full/bounded checker instances. `IsChecker` alone does not supply external soundness: the completeness wrappers separately discharge it. The omega-inconsistent result concerns a context over the original checker. Classical GL uses `dneS`; `iGL` and FairBot retain their documented weaker assumptions. |
| Kripke and arithmetical completeness | `Modal/Basic`, `Deduction`, `Kripke`, `Complete`; `Obj/SolovayCode`, `SolovayStep`, `SolovayLemmas`, `Solovay` | Necessitation applies to theorems, not local modal assumptions. The finite countermodel is nonempty, transitive and irreflexive. The self-referential sentence template uses closed replacements. Solovay's truth lemma and `no_refuted` connect the actual checker and halting soundness to the finite walk; the public and bounded wrappers discharge the generic premises. |
| Letterless results and classical fragment | `Modal/Letterless`, `Obj/Letterless`, `BProvLogic` | Height includes realization of every smaller level; stabilization is from box depth onward, inclusive. `dec` checks every level through that depth, whereas `lim` records eventual truth. The probe `□⊥ → ⊥` has `lim = true`, `dec = false`, and is true but bounded-unprovable. `BProv` refers to the fragment's checker, so unconditional GL completeness does not presume full-theory consistency. |
| Chaitin | `Obj/Chaitin`, `Chaitin` | Least-zero output is functional, even though distinct PR syntax can share a code. Counting uses at most `L + 1` indices, and eventual complexity is proved separately. `chaitin_core` uses a sound and complete checker plus consistency, without halting soundness. The original complexity assertion's number need not be the machine's selected output. Probes check an actual refutable complexity assertion and a common bound beyond which all assertions are true and unprovable. |

## Current drawers

### D2 — Theorem documentation reverses the halting interpretation

Status: open

`Final.lean:10,24–26` and `Extend.lean:214–216` call the true assertion a
"halting sentence," although the conclusion is `notHalts d d.code` and
`¬d.Halts d.code`. They also describe it as "undecided" before introducing
the additional `HaltsSound` hypothesis needed for irrefutability.
`Rosser.lean:350–352,429–430` similarly calls the sentence a halting sentence;
the former says it is false of the machine while the returned `notHalts`
sentence is true. `Second.lean:7,24` calls `Con T` a halting sentence even
though it is `notHalts (conM T) 0`.

These comments are the reader's explanation of the public formal objects.
They must state the same polarity and hypotheses as the theorems. Correct
all these descriptions; distinguish truth and unprovability under consistency
from irrefutability under the additional hypothesis in the Gödel–Kleene
results. Update the second-theorem module introduction to identify its role
as the reduction and point to the completed internal proof in `Obj/Second`.
Keep the formal statements and proofs unchanged for this drawer.

Closure evidence: inspect the corrected comments against their definitions
and theorem types, search the source documentation for the same misuse, and
run the library build. Do not replace every occurrence of "halting sentence"
mechanically: descriptions of `halts` itself can be correct.

### D3 — The supported build emits 307 Lean warnings

Status: open

`nix develop -c lake build` succeeds but currently emits the following
warning inventory on Lean `v4.34.1`, including replayed diagnostics:

| Owner | Deprecated lemmas | Unused variables | Unused simp arguments | Unused section variables | Total |
| --- | --- | --- | --- | --- | --- |
| `Incomplete` | 242 | 4 | 20 | 4 | 270 |
| Imported lean4lean theory | 35 | 1 | 1 | 0 | 37 |

The project warnings span 40 modules. Examples include obsolete `if_pos` /
`if_neg` uses in `NatEnv` and `PRLib`, `dif_pos` / `dif_neg` in `Encode`,
unused simp arguments in `Rules2` and `Obj/BChecker`, and unused section
variables in `Obj/Chain` and `Obj/SolovayStep`. The fork warnings are in
`Lean4Lean/Theory/VExpr.lean` (35 deprecations) and
`Lean4Lean/Theory/Typing/Projection.lean` (two unused-item warnings).

The advertised toolchain upgrade left obsolete proof scripts and noisy
diagnostics throughout the production build. Resolve the entire inventory:
use supported lemma names, remove redundant simp inputs, and correct unused
bindings and section-variable inclusion. Repair the imported theory in the
maintained lean4lean fork, commit that repair, and update this repository's
pin and manifest together. Do not patch `.lake/packages` as the delivered
fix, disable warning/linter reporting, or use the dependency boundary as a
reason to leave its diagnostics unresolved. Preserve the formal results and
their documented hypotheses; update version and dependency documentation
where the repair makes them stale.

Closure evidence: a fresh project build and recompilation of the affected
imported theory emit no warnings on the supported toolchain, and the ordinary
documented build also passes without warnings. Repeat the 48-headline axiom
audit, the whole-namespace allowed-axiom audit, and README statement conformance
checks after the proof-script and dependency edits. Run `nix flake check`.

## Closed drawers

D1 remains closed: hypothesis search passes at indices 0, 1, 2, 16 and
32, and an unsuccessful search permits a fallback proof without a partial
proof or deferred errors. As in the accepted correction, search covers the
explicit context prefix; computed `List.replicate` contexts are normalized
before these probes.

## Verification

The evidence below concerns the judged candidate. It does not close D2 or
D3. `nix flake check` covers hygiene and formatting; the Lean build is a
separate required command.

- `nix develop -c lake build` passed: 153 jobs.
- A fresh temporary package containing copies of every project Lean source,
  `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` built successfully:
  153 jobs, with a new build directory and all project modules compiled.
  It reused the installed pinned dependency packages and their build artifacts;
  this was not a new network fetch or a clean dependency build.
- An audit importing that fresh `Incomplete`, run with
  `lake env lean --trust=0`, checked all 48 `#print axioms` commands from the
  README. Every result is exactly
  `[propext, Classical.choice, Quot.sound]`.
- A separate environment audit checked all 4,048 theorem declarations under
  namespace `Incomplete`, including generated theorems: their axiom
  dependencies are subsets of those three axioms. The audit code is below.
- All 33 displayed README theorem types elaborated against their actual
  constants: each statement's binders were quantified, and `@theoremName`
  supplied a term of the resulting type. This checks the stated types and
  hypotheses, independently of their explanatory prose.
- Disposable `--trust=0` probes passed for zero/nonzero machines, rejection of
  a variable certificate in an empty context, an encoding round trip with a
  projection under a binder, distinct PR syntax with equal codes, the strict
  full/bounded distinction, bounded DNE and consistency, Chaitin refutation and
  eventual true unprovability, `ohyp` success/recovery, bounded `oring`, and
  modal terminal-world and truth/provability boundary cases.
- Source scanning after removing nested and line comments found no `sorry`,
  `admit`, `native_decide`, custom axiom declarations, `unsafe`, `extern` or
  `implemented_by` in the project Lean sources. Object-theory axiom
  constructors are not Lean axiom declarations.
- `nix flake check` passed, running all seven checks: formatting, statix,
  deadnix, gitleaks, shellcheck, actionlint and markers. Disposable probes
  were removed after verification and are not part of the library.

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

## Worker completion requirement

Work from this `REVIEW.md`, resolve D2 and D3, and rewrite this file as the
next `READY FOR REVIEW` submission. Supply exact evidence for each drawer
and identify the finalized candidate as `change / commit`. Follow
`AGENTS.md`: update stale README/version information, run the required Lean
verification and `nix flake check`, commit the candidate, then record its
identity and commit the review submission. Merely replying in chat is not a
submission. The next reviewer must judge both repairs before accepting this
publication cycle.
