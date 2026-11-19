State: RETURNED
Turn: worker
Candidate: qpnltmnrxuwykqzzqpyptnzxkrnzsyvl / f4778a940af90469db7480a5d4dc0e0b3e06d54a

# Publication review of the README and tooling

## Objective

Make the public claims match the Lean theorems and make source links reliable
through ordinary edits. Reviewed the eight commits after both pushed
remote-tracking bookmarks at `b567dcd48eb8`. The prior publication candidate
`49771b318eb6` is accepted at the user's direction. D1 remains closed, and D2
and D3 are closed. The returned findings concern the subsequent README and
tooling changes.

## Accepted foundation

The project targets the pinned lean4lean declarative judgment. The full
results concern well-formed extensions of `natEnv`. The unconditional
results concern the bounded judgments for `natEnv` and `clEnv`, with the
fragment's own checker for bounded provability. Preserve the formal
statements and the package's documented Lean and dependency pins.

## Current findings

### D4 — The README scope and matrix overstate the formal results

Status: open

- README line 14 asserts a limit on Lean's full universe hierarchy.
  `second_incompleteness` in `Incomplete/Obj/Second.lean` applies to a
  consistent well-formed environment extending `natEnv` and concerns its
  specific internal consistency sentence. Introduce the two regimes through
  that formal scope.
- The matrix pairs second incompleteness and the ω-inconsistent context with
  one bounded result (line 23). `bcon_iterated` supplies bounded second
  incompleteness at `n = 0`. `omega_inconsistent` is the full-judgment result
  with a hypothesis context. Give each result its own row and spell out
  which common structural and statement-local premises the headings omit.
  The “None” entries currently sit beside source signatures that take
  premises such as `TablesFor` and proposition typing.
- The letterless prose calls the tower finite (line 89), while
  `bprovable_iff_lvl` quantifies over every natural level.
  `Modal.dec` checks a finite prefix through the box depth, using
  stabilization. Also narrow line 222 to the proved separation of
  letterless GL from iGL. `Modal.not_iGL_dne_box` does not establish that
  proving `dneS` is necessary for an object theory to realize the GL theorem.
- Line 32 says all theorems live in `Incomplete`, while the README itself
  links to the root-qualified extension `Lean4Lean.VEnv.WF.checkable`.
  Qualify the namespace description.

Check the revised scope, matrix and letterless prose against the named
theorems and `Modal.dec` before resubmitting.

### D5 — A routine format run leaves stale anchors after Lean-only edits

Status: open

`nix/formatter.nix` registers the source-dependent anchor rewriter for
Markdown inputs only. Treefmt's ordinary cache skips an unchanged README
even though the referenced Lean file has moved. In a disposable jj checkout
using the exact built flake formatter, the first run wrote `A.lean#L1` for
`alpha`. Inserting a comment before the theorem and rerunning the formatter
left `#L1` intact. The check wanted `#L2`. A third run with `--no-cache`
repaired the link.

Make the normal repository formatting entry point refresh anchors after
source-only edits. Document the edit, format, and check sequence and the
syntax contributors use for managed links. Demonstrate that two ordinary
format runs with only a Lean line insertion between them repair the anchor
and that the resulting tree passes both flake link checks.

### D6 — Reference-style Lean links bypass both checks

Status: open

The anchor checker scans one physical line for inline links in
`nix/lean-anchors.py`. Lychee tests whether a Lean file exists, but does not
validate its line fragments. In a file with the single-line theorem `alpha`,
the reference link below passed both checks and survived the exact formatter
with its stale fragment:

```markdown
[`alpha`][decl]

[decl]: A.lean#L999
```

A multiline inline link with the same destination also passed. In addition,
an ordinary Markdown title such as `[Source](A.lean "A human-readable tooltip")` is interpreted as a Lean symbol and fails even though the file
link is valid.

Ensure a rendered local Lean line link is checked or rejected with a
diagnostic directing the author to the supported syntax. Use a recognizable
symbol marker that distinguishes anchor metadata from ordinary link titles.
Show a positive control for current README links and negative controls for
a stale inline anchor, a stale reference or multiline link, and an unknown
symbol. Show that plain file links with human-readable titles still pass.
Lychee already catches missing local files and missing Markdown headings in
the corresponding negative controls.

## Verification

- The documented Lean build and `nu tasks.nu check` pass. A disposable
  build from source, using both manifest revisions and no Lake build
  artifacts, completed 153 jobs with zero warnings. The exact fork pin is
  publicly reachable.
- All 33 displayed theorem signatures elaborate to definitionally equal types
  under `--trust=0`. All 16 displayed definition bodies were checked against
  the library definitions, using structural induction for `Modal.lvl`.
- Lean's declaration metadata confirms the source module and selection line
  for all 47 README symbol links.
- All 48 published axiom checks report exactly
  `[propext, Classical.choice, Quot.sound]`. The namespace audit checked
  4,048 theorems and found only permitted dependencies.

## Worker completion

Work from this `REVIEW.md` and resolve D4–D6. Run the verification for each
finding and the checks in `AGENTS.md`. Commit the candidate, rewrite this
file as a `READY FOR REVIEW` submission with the exact candidate change and
commit IDs plus the evidence for each finding, and commit the submission.
A chat reply alone does not submit the candidate.
