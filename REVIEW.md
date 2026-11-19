State: READY FOR REVIEW
Turn: reviewer
Candidate: zxlkvmuzwpnotnytyrsqsspnknoozqwt / 34e2e6100271e43218c6a62c003a0165c596f2ad

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

Status: submitted

The placeholder scan is gone. `process_md` parses the unmodified file, and
that parse alone decides what renders. `located_link` wraps markdown-it's
inline `link` rule. On each successful non-silent match, it records the
link's span within the inline content on the `link_open` token. It also
records the destination span: the rule's own `parseLinkLabel` and
`parseLinkDestination` re-run from the match start, and the span is kept
only for an inline (not reference) link.

`align` maps each inline content line to its source line. It allows only
deletions: container prefixes, cell delimiters, and the backslash of a
table-cell `\|`. A per-line cursor keeps table cells in order, and a
failed alignment disables later lookups on that line. A rendered link
needs validation when it has a `lean:` title, a single code-span symbol
label, or a fragment. Such a link is then

- rejected as multiline if its own content span contains a newline;
- rejected with a location diagnostic if its destination cannot be
  mapped, or if the mapped source bytes differ from the parsed
  destination;
- otherwise validated or rewritten only at that destination's source
  span.

The file is read and written with `newline=""`, so the rewrite keeps every
byte outside the replaced destinations, line endings included. Parsed-HTML
`href` checks and decoded-path classification are unchanged.

`checks.lean-anchors-test` now compares bytes and has 35 cases, each with
an expected outcome:

- **ok**: `--check` passes, and the write pass changes nothing.
- **fix**: `--check` exits 1 and names `README.md:<line>`. The write pass
  produces exactly the expected bytes, which then pass `--check`.
- **reject**: `--check` and the write pass both exit 1 and name
  `README.md:<line>`. The bytes are unchanged.

New cases:

- Fixed: `` `example ](text` `` followed by a stale `#L99` anchor and by
  an omitted anchor. Only the rendered URL changes to `A.lean#L1`.
- Rejected: `` [`alpha`](A.lean#L1\n) `` (line 3 of its fixture) and
  `[text](A.lean#L1\n "lean:alpha")`.
- Fixed: a CRLF file with a trailing-space hard break and an escaped
  literal. One URL is rewritten, and the output is byte-identical
  otherwise, CRLF included.
- Fixed: a table cell containing an escaped pipe before the link, and a
  link inside a list item inside a blockquote.

The previous 28 cases remain, now with line-level diagnostic assertions.
Run against `nix/lean-anchors.py` from `05a0eb35`, the harness fails 5
cases: both inline-code cases, both multiline cases, and CRLF. The
candidate passes all 35.

The built flake formatter ran `--ci` twice in a disposable jj repository
on the stale inline-code README. The first run exited 1 ("unexpected
changes detected") after rewriting only `#L99` to `#L1`. The second run
exited 0.

## Verification

- `nix flake check` passed all ten checks. `nix develop -c lake build`
  completed 153 jobs. `nix fmt` changes nothing on the candidate.
- Stripped all 61 README `#L…` fragments in a disposable copy. The anchor
  pass reproduced `README.md` byte for byte.
- Lean sources, README, and package pins are unchanged from `05a0eb35`.
