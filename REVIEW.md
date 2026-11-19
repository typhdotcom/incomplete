State: RETURNED
Turn: worker
Candidate: mmrrnmvqzrrnntmvxruvowslzlsxrwmm / 05a0eb35cf432b8284792ee8e71838fb3aadd60c

# Publication review of the README and tooling

## Objective

Keep the public claims aligned with the Lean theorems and keep declaration
links reliable through ordinary edits. This verdict judges the candidate
submitted in `7b88c95a3868`. The prior publication candidate `49771b318eb6`
remains accepted. Preserve the pinned lean4lean declarative judgment, the full
and bounded provability results, and the supported build.

## Closed

- D1, D2, D3, and D4 remain closed.
- D5 closed. The built flake formatter refreshed the tracked README after a
  Lean-only line insertion in a disposable jj repository. Both `--ci` and
  `--fail-on-change` returned 1 for stale anchors and 0 after updating them.
  `--formatters nixfmt` left the stale Markdown untouched. Files in the
  ignored directory and nested jj repository retained their checksums, and
  the invalid link in the ignored file did not block formatting.

## Current finding

### D6 — Use the original Markdown parse to establish link identity

Status: open

The 28 fixtures pass and exercise the previous review's counterexamples.
The new placeholder scan, however, changes the source before deciding
which links render. With `alpha` on line 1 of `A.lean`, this ordinary
Markdown renders a link to line 99:

```markdown
`example ](text` and [`alpha`](A.lean#L99)
```

The scan treats the closing backtick as part of a potential destination and
replaces it with a placeholder. This changes how Markdown parses the rest
of the line and hides the real link. The anchor checker, the built
formatter with `--ci`, and Lychee all exited 0 and left the stale link intact.
Removing `#L99` also leaves a managed link that the formatter never anchors.

The scan also records the URL span without establishing whether the whole
link is on one line. These two rendered links both pass despite the README's
single-line rule:

```markdown
[`alpha`](A.lean#L1
)

[text](A.lean#L1
 "lean:alpha")
```

Finally, the anchor rewrite changes the entire file's CRLF line endings to
LF when it updates one URL. This violates the promise that edits touch only
the linked destination. The existing text-mode fixture harness cannot see
that difference.

Use the unmodified Markdown as the authority for what renders. Obtain
destination spans from the parser's inline-link rule and map them back to
the original source. Only rewrite a supported rendered link after locating
its own destination, and use the full link's source range to enforce the
single-line rule. Report a diagnostic when a rendered fragment needs
validation and the source location cannot be established. Preserve the
original line endings and all bytes outside rewritten destinations. Keep
the existing parsed-HTML and decoded-path checks.

Add the inline-code case with both a stale and an omitted anchor, and
verify that the stale check fails and the formatter repairs only the
rendered URL. Add the two multiline cases and an exact byte comparison
for a CRLF rewrite. Retain the previous fixture coverage, verify rejected
links produce link diagnostics, and rerun the built formatter in CI mode
on the stale inline-code case.

## Verification

- Ran the 28-fixture suite and all ten flake checks. The documented Lean
  build completed 153 jobs with zero warnings. `nix fmt` changed no files
  in the submitted checkout.
- Stripped all 61 README source fragments in a disposable copy. The
  anchor formatter reproduced the original README byte for byte. Lean
  sources, theorem snippets, and package pins match the accepted review.

## Worker completion

Work from this `REVIEW.md` and resolve D6. Run the listed regressions and
follow `AGENTS.md`. Commit the candidate, rewrite this file as a
`READY FOR REVIEW` submission with the exact candidate change and commit
IDs and evidence for D6, and commit the submission. A chat reply alone
does not submit the candidate.
