State: READY FOR REVIEW
Turn: reviewer
Candidate: mmrrnmvqzrrnntmvxruvowslzlsxrwmm / 05a0eb35cf432b8284792ee8e71838fb3aadd60c

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

Status: submitted

The wrapper's recursive prepass and argument parser are gone.
`lean-anchors` stays a treefmt formatter at priority 0, and the wrapper
runs `treefmt --walk "$walk" --no-cache "$@"`.

Probe: a scratch jj repo whose tracked `README.md` links
`` [`alpha`](A.lean#L1) ``, an ignored `scratch/x.md` with the invalid
link `[x](A.lean#L5)`, and a nested jj repo with `nested/n.md`. Each run
used the built flake formatter. Between runs, a blank line was prepended
to `A.lean`.

| run                                | exit | README anchor | ignored / nested |
| ---------------------------------- | ---- | ------------- | ---------------- |
| `fmt` twice (alpha at L1)          | 0, 0 | `#L1`         | unchanged        |
| `fmt` (alpha at L2)                | 0    | `#L2`         | unchanged        |
| `fmt --ci` (alpha at L3)           | 1    | `#L3`         | unchanged        |
| `fmt --ci` again                   | 0    | `#L3`         | unchanged        |
| `fmt --formatters nixfmt` (L4)     | 0    | `#L3`         | unchanged        |
| `fmt --fail-on-change`, then rerun | 1, 0 | `#L4`         | unchanged        |

The ignored invalid link no longer blocks the run, and selecting only
`nixfmt` leaves Markdown alone. The `nu tasks.nu fmt` and
`nu tasks.nu check` commands are unchanged.

### D6 — Validate each rendered destination and preserve literal examples

Status: submitted

`process_md` finds every inline destination span that follows `](` and
replaces each span with a unique probe URL. It parses the probed text once
with markdown-it (CommonMark with tables and strikethrough). A rendered
`link_open` whose href is a probe owns exactly that source span. If a probe
does not render, its span is literal text, and its bytes are never
validated or edited. Rewrites touch only the URL span of a managed link.
The symbol comes from the token: a `lean:` title, or a label made of a
single `code_inline` token.

Every other rendered link is classified the same way, including
reference links and probe URLs mapped back through markdown-it's
`normalizeLink(unescapeAll(raw))`. A link is local Lean when
`urlsplit(href)` has no scheme or netloc and its percent-decoded path ends
in `.lean`. The fragment rule applies to that classification. A managed
link's raw URL must have the form `path.lean[#fragment]` with no query,
escape, entity, or percent-encoding. Any other rendered Lean
symbol or line link fails with `USAGE_HINT`. HTML blocks and inline HTML
go through `html.parser`, so comments are skipped and only real `href`
attributes are decoded and checked.

`checks.lean-anchors-test` (`nix/lean-anchors-test.py`) runs 28 fixtures
against `A.lean`. Each fixture checks the `--check` exit status, confirms
that check mode leaves the bytes alone, and checks the write-pass exit
status and the exact bytes afterward. Rewritten fixtures must then pass
`--check`.

- These fixtures must fail and stay untouched: the escaped example beside
  a rendered multiline link; `A.lean?view=1#L999`; `A.le&#97;n#L999`;
  `<a data-href="README.md" href="A.lean#L999">`; an HTML `href` of
  `A.le&#97;n#L999`; plain HTML line links; and the original controls
  (reference with fragment, reference with `lean:` title, multiline,
  unmanaged fragment, empty `lean:` title, unknown symbol, missing file).
- These pass with their bytes unchanged: `` \[`alpha`](A.lean) ``, the
  same example in a four-space indented block, a fenced block holding a
  stale anchor, inline code spans, an HTML comment holding a stale anchor,
  an HTML file link with a fragment in another attribute, ordinary
  tooltips, and plain file links.
- These are refreshed, and only the rendered span changes: stale and
  missing anchors in both managed forms, table cells, and an escaped
  literal beside an identical rendered link.

Run against the previous `nix/lean-anchors.py` from `01579c8c`, the
harness fails 8 cases: the masked multiline link, the query, the
`data-href` and entity HTML links, the HTML comment, the escaped and
indented examples, and the literal beside a rendered link. The new tool
passes 28 of 28.

To check the README, every `#L…` fragment was stripped from a copy and
the formatter was run on it. The output was byte-identical to `README.md`,
so all 61 README symbol links are managed and resolve to their current
spans.

## Verification

- `nix develop -c lake build` completed 153 jobs. The Lean sources are
  unchanged from the accepted candidate.
- `nix flake check` passed all ten checks, including the new
  `lean-anchors-test`. `nix fmt` is a no-op on the candidate.
- README change: the tooling paragraph now lists the rejected link
  forms and states that escaped and code-span examples are left as
  written.
