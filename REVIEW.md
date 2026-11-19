State: READY FOR REVIEW
Turn: reviewer
Candidate: rwnxlnsynvsorxwwoxlnoxvoytwwqnqv / c60eb62977ee214609f9c3726110178d0705ecda

# Publication review of the README and tooling

## Objective

Make the public claims match the Lean theorems and make source links reliable
through ordinary edits. The prior publication candidate `49771b318eb6` is
accepted; D1, D2, and D3 remain closed. This submission resolves D4–D6 from the
returned review `tlvmqwql` / `1185e21e` in candidate commit
`rwnxlnsynvsorxwwoxlnoxvoytwwqnqv` / `c60eb62977ee214609f9c3726110178d0705ecda`.

## Accepted foundation

The project targets the pinned lean4lean declarative judgment. The full
results concern well-formed extensions of `natEnv`. The unconditional
results concern the bounded judgments for `natEnv` and `clEnv`, with the
fragment's own checker for bounded provability. Formal statements and the
package's documented Lean and dependency pins are unchanged.

## Current findings

### D4 — The README scope and matrix overstate the formal results

Status: resolved, awaiting review

- **Scope framing (`README.md:14–17`)**: Removed the informal claim about
  Lean's full universe hierarchy. [README.md](README.md#scope) now introduces
  full provability (`Provable env` over `env.WF` and `natEnv ≤ env`, noting
  that consistency and halting soundness are unproved hypotheses and that
  [`second_incompleteness`](Incomplete/Obj/Second.lean#L200-L203) shows no consistent
  well-formed extension of `natEnv` proves its internal consistency sentence
  `Con T`) alongside bounded provability (`BProvable` over `natEnv` and
  `clEnv`, whose consistency and Σ₁-soundness come from the ZF set model in
  [ModelSound.lean](Incomplete/ModelSound.lean)).
- **Hypothesis matrix (`README.md:19–31`)**:
  - `README.md:19` explicitly states what the matrix columns omit: every
    full-judgment row also takes `env.WF` and `natEnv ≤ env` (or `env.WF' ds`
    with `.induct natDecl ∈ ds`); statements mentioning `Con T`, `Prov T`, or
    `A.real T σ` take `TablesFor env T` (naming the exact exceptions
    [`prov_mp_provable`](Incomplete/Obj/Derivability.lean#L140-L142), which holds for
    arbitrary `T : Tables`, and
    [`second_incompleteness`](Incomplete/Obj/Second.lean#L200-L203) and
    [`omega_inconsistent_exists`](Incomplete/Obj/Omega.lean#L60-L64), which construct
    `T` from `hwf.checkable.tables`); and statements quantified over object
    propositions or modal realizations take closed-proposition typing
    (`env.HasType 0 [] · (.sort .zero)` in `VEnv`,
    `BDefEq clEnv [] · · (.sort .zero)` in `clEnv`) and `A.Letterless` where
    stated.
  - **2nd incompleteness** (`README.md:25`) and **Consistent, ω-inconsistent
    context** (`README.md:26`) now occupy separate rows: row 25 pairs
    `second_incompleteness` and `con_unprovable` with `bcon_iterated` at
    `n = 0` (`¬BProvable clEnv (BProv ⊥ → ⊥)`), while row 26 records
    `omega_inconsistent` as a full-judgment result (`—` in the bounded column).
    Rosser (`README.md:24`) and Löb / D1–D3 / FairBot / iGL (`README.md:27`)
    likewise state their exact bounded coverage (`IsChecker.bounded` for Löb,
    D1–D3, and iGL).
- **Letterless tower vs. finite prefix & iGL separation (`README.md:92`, `193`, `225`)**:
  `README.md:92` states that `Modal.lvl n A` is indexed by every natural level
  `n : Nat` (the ω-tower in `bprovable_iff_lvl` and `provable_iff_lvl`),
  stabilizes at `Modal.lim A` from box depth `Modal.bd` onward
  (`Modal.lvl_eq_lim`), and is decided by `Modal.dec` checking the finite
  prefix `n ≤ bd A` (`bprovable_iff_dec`, `provable_iff_dec`). `README.md:225`
  states strictly what `Modal.not_iGL_dne_box` proves: `GL (¬¬□⊥ → □⊥)` and
  `¬iGL (¬¬□⊥ → □⊥)` via a three-element Heyting modal algebra.
- **Namespace qualification (`README.md:35`)**: Qualified the namespace note
  to `Incomplete` (including `Incomplete.Modal`, with `Incomplete.Obj` opened
  for `Thm`, `neg`, `prfT`, `numT`, `=ₒ`, and `↔ₒ`), noting explicitly that
  [`Lean4Lean.VEnv.WF.checkable`](Incomplete/Extend.lean#L207) lives in `Lean4Lean`.

### D5 — A routine format run leaves stale anchors after Lean-only edits

Status: resolved, awaiting review

- **Formatter wrapper (`nix/formatter.nix:153–207`)**: Because `treefmt`'s
  per-file cache does not track cross-file `.lean` → `.md` anchor dependencies,
  the `formatter` wrapper now runs [nix/lean-anchors.py](nix/lean-anchors.py)
  up front across `"${root:-.}"` (or explicit positional paths; `--check` under
  `--fail-on-change`) before `exec treefmt`. When a `.lean` edit shifts a
  declaration, `lean-anchors.py` rewrites the referencing Markdown file on
  disk, after which `treefmt` sees the updated file and runs `mdformat` to
  settle table widths in the same invocation.
- **Workflow documentation (`README.md:283–291`)**: Documented the edit →
  `nu tasks.nu fmt` (`nix fmt`) → `nu tasks.nu check` (`nix flake check`)
  sequence and the managed link syntax in [README.md](README.md#build-and-audit).
- **Closure test**: Built `.#formatter.x86_64-linux`
  (`/nix/store/d1qm3asm5pg8pa0fdf2zh6z62dr2q4ig-treefmt/bin/treefmt`) and ran
  two ordinary cached invocations (shared `XDG_CACHE_HOME`, no `--no-cache`) in
  a disposable `jj git init --colocate` checkout:
  1. With `theorem alpha : True := trivial` on line 1 of `A.lean` and
     `` [`alpha`](A.lean) `` plus `[Alpha](A.lean "lean:alpha")` in
     `README.md`, Run 1 rewrote both links to `A.lean#L1`.
  2. After prepending `-- inserted line` to `A.lean` without touching
     `README.md`, Run 2 rewrote both links to `A.lean#L2`.
  3. Running `lean-anchors.py --check` and
     `lychee --offline --no-progress --include-fragments .` on the resulting
     tree both exited `0`.

### D6 — Reference-style Lean links bypass both checks

Status: resolved, awaiting review

- **Distinct `lean:` title marker & CommonMark AST audit ([nix/lean-anchors.py](nix/lean-anchors.py))**:
  - Link titles now act as symbol anchors only when prefixed with `lean:`
    (`[label](Incomplete/File.lean "lean:symbol")`); titles without `lean:` are
    left untouched as ordinary tooltips on plain file links. Single-line
    code-span labels without a title (`` [`symbol`](Incomplete/File.lean) ``)
    remain supported.
  - Added `audit_ast_links` using `markdown-it-py` (`MarkdownIt("commonmark")`),
    inspecting rendered `link_open` tokens, `env["references"]` definitions,
    and raw HTML `<a href=...>` tags. Every local `.lean` link carrying a `#`
    fragment or `lean:` title that is not accounted for by a validated
    single-line inline managed link fails both formatting and `--check` with a
    diagnostic directing the author to
    `` single-line [`symbol`](path.lean) or [text](path.lean "lean:symbol") ``.
- **Positive and negative controls** (exercised against the built flake
  formatter and `lean-anchors.py --check` + `lychee`):
  - *Positive — repository links*: All 61 managed symbol links in
    [README.md](README.md) pass `checks.lean-anchors` and match Lean's
    `findDeclarationRanges?` (`selectionRange.pos.line` and module path);
    `checks.links` (`lychee --offline --no-progress --include-fragments .`)
    exits `0`.
  - *Positive — human-readable file tooltip*:
    `[Source](A.lean "A human-readable tooltip")` survives formatting unchanged
    and passes both `lean-anchors.py --check` and `lychee`.
  - *Negative — stale / unmanaged inline*: `` [`alpha`](A.lean#L999) `` fails
    `--check` (`A.lean#L999 -> expected A.lean#L2 for 'alpha'`);
    `[Source](A.lean#L999 "A human-readable tooltip")` fails both formatter and
    `--check` (`unmanaged fragment on .lean link; use single-line ...`).
  - *Negative — stale reference-style link*: `` [`alpha`][decl] `` with
    `[decl]: A.lean#L999` fails both formatter and `--check`
    (`[DECL]: A.lean#L999: reference-style Lean symbol/line links are unsupported; use single-line ...`).
  - *Negative — stale multiline inline link*: multiline
    `` [`alpha`]( A.lean#L999 ) `` fails both formatter and `--check`
    (`A.lean#L999: unmanaged or multiline Lean line link; use single-line ...`).
  - *Negative — HTML anchor*: `<a href="A.lean#L999">alpha</a>` fails both
    formatter and `--check` (`HTML <a> Lean line links are unsupported; ...`).
  - *Negative — unknown symbol*: `` [`no_such_thm`](A.lean) `` and
    `[Label](A.lean "lean:no_such_thm")` fail both formatter and `--check`
    (`A.lean: symbol 'no_such_thm' not found`).

## Closed drawers

D1, D2, and D3 remain closed from `49771b318eb6`. No Lean source file,
`lakefile.toml`, `lake-manifest.json`, or `lean-toolchain` changed in this
candidate.

## Verification

Run on candidate `rwnxlnsynvsorxwwoxlnoxvoytwwqnqv` /
`c60eb62977ee214609f9c3726110178d0705ecda`:

- `nix develop -c lake build`: completed 153 jobs, 0 warnings.
- `nix flake check`: all 9 checks pass (`formatting`, `links`, `lean-anchors`,
  `statix`, `deadnix`, `gitleaks`, `shellcheck`, `actionlint`, `markers`).
- Statement and definition conformance (`lake env lean --trust=0`): all 33
  displayed `theorem` signatures pass `isDefEq` against the exported constants,
  and all 16 displayed `def` / `structure` bodies match the library
  definitions.
- Symbol-link metadata check (`lake env lean --trust=0`): all 61 symbol links
  in `README.md` (and those in this `REVIEW.md`) match Lean's module index and
  `findDeclarationRanges?` selection line.
- Axiom audit (`lake env lean --trust=0`): all 48 published `#print axioms`
  commands report `[propext, Classical.choice, Quot.sound]`, and the
  whole-namespace audit verified all 4,048 `Incomplete` theorems use only
  permitted axioms.
