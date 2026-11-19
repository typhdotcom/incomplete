#!/usr/bin/env python3
import subprocess
import sys
import tempfile
from pathlib import Path

TOOL = Path(sys.argv[1])
LEAN = "theorem alpha : True := trivial\n\ntheorem beta :\n    True := trivial\n"

# (name, markdown, expected exit of --check, expected text after a write pass)
CASES = [
    ("label form", "[`alpha`](A.lean#L1)\n", 0, None),
    ("title form", '[the theorem](A.lean#L3-L4 "lean:beta")\n', 0, None),
    ("label form refresh", "[`alpha`](A.lean#L9)\n", 1, "[`alpha`](A.lean#L1)\n"),
    ("label form added", "[`beta`](A.lean)\n", 1, "[`beta`](A.lean#L3-L4)\n"),
    (
        "title form refresh",
        'x [t](A.lean#L1 "lean:beta") y\n',
        1,
        'x [t](A.lean#L3-L4 "lean:beta") y\n',
    ),
    ("plain file link", "[A.lean](A.lean) [`A.lean`](A.lean)\n", 0, None),
    ("ordinary tooltip", '[`alpha`](A.lean "a file")\n', 0, None),
    ("unknown symbol", "[`gamma`](A.lean#L1)\n", 1, ""),
    ("missing file", "[`alpha`](B.lean#L1)\n", 1, ""),
    ("unmanaged fragment", "[text](A.lean#L1)\n", 1, ""),
    ("empty lean title", '[t](A.lean#L1 "lean:")\n', 1, ""),
    ("reference", "[`alpha`][r]\n\n[r]: A.lean#L1\n", 1, ""),
    ("reference title", '[x][r]\n\n[r]: A.lean "lean:alpha"\n', 1, ""),
    ("multiline", "[`alpha`](\nA.lean#L1)\n", 1, ""),
    (
        "escaped masks multiline",
        "\\[`alpha`](A.lean#L1) [intentionally wrong](\nA.lean#L1)\n",
        1,
        "",
    ),
    ("query", "[`alpha`](A.lean?view=1#L999)\n", 1, ""),
    ("entity", "[`alpha`](A.le&#97;n#L999)\n", 1, ""),
    ("html", '<a href="A.lean#L1">alpha</a>\n', 1, ""),
    (
        "html data-href first",
        '<a data-href="README.md" href="A.lean#L999">alpha</a>\n',
        1,
        "",
    ),
    ("html entity", '<a href="A.le&#97;n#L999">alpha</a>\n', 1, ""),
    ("html comment", '<!-- <a href="A.lean#L999">alpha</a> -->\n', 0, None),
    ("html file link", '<a data-x="A.lean#L1" href="A.lean">alpha</a>\n', 0, None),
    ("escaped", "\\[`alpha`](A.lean)\n", 0, None),
    ("indented code", "para\n\n    [`alpha`](A.lean)\n", 0, None),
    ("fenced code", "```markdown\n[`alpha`](A.lean#L9)\n```\n", 0, None),
    ("inline code", "`[`alpha`](A.lean)` and ``[`alpha`](A.lean)``\n", 0, None),
    (
        "table",
        "| a | b |\n| - | - |\n| [`alpha`](A.lean#L2) | [`beta`](A.lean) |\n",
        1,
        "| a | b |\n| - | - |\n| [`alpha`](A.lean#L1) | [`beta`](A.lean#L3-L4) |\n",
    ),
    (
        "literal beside rendered",
        "\\[`alpha`](A.lean) [`alpha`](A.lean)\n",
        1,
        "\\[`alpha`](A.lean) [`alpha`](A.lean#L1)\n",
    ),
]


def run(*args: str) -> int:
    return subprocess.run(
        [sys.executable, str(TOOL), *args], capture_output=True
    ).returncode


failures = 0
for name, md, want_check, want_write in CASES:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "A.lean").write_text(LEAN)
        readme = root / "README.md"
        readme.write_text(md)
        got_check = run("--check", str(readme))
        unchanged = readme.read_text() == md
        got_write = run(str(readme))
        after = readme.read_text()
        expect_after = md if want_write in (None, "") else want_write
        ok = (
            got_check == want_check
            and unchanged
            and got_write == (1 if want_write == "" else 0)
            and after == expect_after
        )
        if want_write not in (None, ""):
            ok = ok and run("--check", str(readme)) == 0
        if not ok:
            failures += 1
            print(
                f"FAIL {name}: check={got_check} write={got_write} after={after!r}",
                file=sys.stderr,
            )
print(f"{len(CASES) - failures}/{len(CASES)} lean-anchors cases passed")
sys.exit(1 if failures else 0)
