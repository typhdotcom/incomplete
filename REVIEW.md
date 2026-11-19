State: COMPLETE
Turn: none
Candidate: zxlkvmuzwpnotnytyrsqsspnknoozqwt / 34e2e6100271e43218c6a62c003a0165c596f2ad

# Publication review of the README and tooling

The publication candidate submitted in `8512b7d020f8` is accepted. The
README describes the formal scope of the Lean results, the pinned build
and audit commands, and the syntax for managed declaration links.

## Closed

- D1, D2, and D3 remain closed from the prior publication review.
- D4 closed. The README distinguishes full and bounded provability, states
  the premises of each result, and describes the finite check for the
  letterless tower and the proved GL/iGL separation.
- D5 closed. The flake formatter refreshes tracked links after a Lean-only
  edit through treefmt's existing file selection. Stale anchors yield an
  unsuccessful CI run before the next clean run. Ignored files, nested
  repositories, and Markdown outside the selected formatters stayed
  unchanged in the disposable repository probes.
- D6 closed. The link checker determines which links render from the
  original Markdown parse, checks the complete link for line breaks, and
  rewrites the mapped destination bytes. The CRLF fixture preserves all
  other bytes. A link in a list continuation with a partially consumed
  indentation tab can trigger the source-location diagnostic and leave
  the file unchanged. The space-indented form passes.

## Verification

- All ten flake checks and all 35 anchor fixtures passed. The previous
  checker failed the five regression fixtures covering inline code before
  a real link, multiline links, and CRLF preservation.
- The built formatter's CI run on the inline-code counterexample exited
  1 and changed only `#L99` to `#L1`. The second run exited 0.
- The anchor pass regenerated all 61 README fragments byte for byte in a
  disposable copy. The Lean sources, theorem snippets, and dependency
  pins match the previous review. The documented Lean build completed
  153 jobs, and `nix fmt` changed no files.
