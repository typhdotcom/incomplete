State: RETURNED
Turn: worker
Candidate: rwnxlnsynvsorxwwoxlnoxvoytwwqnqv / c60eb62977ee214609f9c3726110178d0705ecda

# Publication review of the README and tooling

## Objective

Make the public claims match the Lean theorems and keep declaration links
reliable through ordinary edits. This verdict judges the candidate submitted
in `7c1926c38949`. The prior publication candidate `49771b318eb6` remains
accepted. The project targets the pinned lean4lean declarative judgment.
Preserve the full and bounded provability results and the pinned build.

## Closed

- D1, D2, and D3 remain closed.
- D4 closed. The revised scope describes full and bounded provability,
  distinguishes the second theorem from the ω-inconsistent context in the
  matrix, explains box-depth stabilization and the finite decision check,
  and reports the exact GL/iGL separation. The namespace note identifies the
  `Lean4Lean.VEnv.WF.checkable` extension. The revised text agrees with the
  cited declarations.

## Current findings

### D5 — Refresh anchors within treefmt's selected files

Status: open

Two ordinary formatter runs with a Lean-only line insertion between them
now update the tracked README from `A.lean#L1` to `A.lean#L2`.
The wrapper's independent directory walk also rewrites ignored Markdown
and Markdown in nested repositories, including files the jj walker omits.
An invalid link in an ignored scratch directory blocks an ordinary
repository format run. Selecting only `nixfmt` still rewrites anchors.
With a stale anchor, the wrapper's `--ci` invocation rewrites the README
before treefmt sees it and exits successfully, even though treefmt's CI
mode enables `--fail-on-change`.

Remove the recursive prepass and its argument parser. Keep the anchor
rewriter in treefmt with its current priority and run treefmt without its
per-file cache on the normal formatter path. In the disposable jj probe,
invoking the configured treefmt with `--walk jujutsu --no-cache` refreshed
the tracked README through the Lean-only change, left ignored and nested
files alone, and returned exit 1 in CI mode when the README needed an update.
Verify the same behavior through the flake's formatter and confirm that
`--formatters nixfmt` leaves Markdown alone. Keep the documented format
and check commands.

### D6 — Validate each rendered destination and preserve literal examples

Status: open

The `lean:` marker, ordinary title handling, and direct reference and
multiline rejection probes pass. The checker still correlates rendered
links with raw text matches by destination and title across a paragraph.
With `alpha` on line 1 of `A.lean`, this file passes the anchor checker
and Lychee, although only the second occurrence is a link and it uses the
unsupported multiline form:

```markdown
\[`alpha`](A.lean#L1) [intentionally wrong](
A.lean#L1)
```

Given an escaped example without a fragment, formatting rewrites
`` \[`alpha`](A.lean) `` and the same example in a four-space-indented code
block. Both render as text. The HTML regex inspects markup
inside comments and accepts this rendered stale link because it matches
`data-href` first:

```html
<a data-href="README.md" href="A.lean#L999">alpha</a>
```

An HTML destination of `A.le&#97;n#L999` and the Markdown destination
`A.lean?view=1#L999` also pass both checks. Their parsed URL path is
`A.lean`, so both belong to the advertised local-line-link rule.

Use Markdown tokenization to associate every managed link with its own
source span before validating or editing it. Use HTML attribute parsing
for actual anchors and classify local URLs by their decoded path before
applying the fragment rule. Reject unsupported rendered Lean line links
with the existing syntax guidance. Demonstrate that the examples above
fail when they contain a rendered unsupported link. Verify that escaped
links, code blocks, HTML comments, and ordinary tooltips pass and retain
their original bytes during the anchor pass. Rerun the original positive
and negative controls, including the two managed forms, the existing
README links, stale anchors, references, and unknown symbols.

## Verification

- The documented Lean build completed 153 jobs with zero warnings.
  All nine flake checks passed for the submission.
- The Lean code blocks changed only in a comment. Rechecked all 33
  displayed theorem signatures and the 16 definition bodies under
  `--trust=0`. All 61 README symbol links agree with Lean's declaration
  metadata for the module and selection line.
- All 48 published axiom checks returned
  `[propext, Classical.choice, Quot.sound]`. The namespace audit again
  checked 4,048 theorems and found only permitted dependencies.

## Worker completion

Work from this `REVIEW.md` and resolve D5 and D6. Run the verification for
each finding and follow `AGENTS.md`. Commit the candidate, then rewrite
this file as a `READY FOR REVIEW` submission with the exact candidate
change and commit IDs and evidence for both findings. Commit the
submission. A chat reply alone does not submit the candidate.
