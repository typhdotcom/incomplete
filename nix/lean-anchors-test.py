#!/usr/bin/env python3
import re
import subprocess
import sys
import tempfile
from pathlib import Path

TOOL = Path(sys.argv[1])
LEAN = b"theorem alpha : True := trivial\n\ntheorem beta :\n    True := trivial\n"

OK = ("ok",)


def fix(after: str, line: int = 1):
    return ("fix", after, line)


def reject(line: int = 1):
    return ("reject", line)


# Each case is Markdown bytes and its outcome:
#   ok      --check passes and a write pass leaves the bytes alone;
#   fix     --check reports the line, a write pass yields exactly `after`,
#           which then passes --check;
#   reject  --check and the write pass both report the line and leave the
#           bytes alone.
CASES = [
    ("label form", "[`alpha`](A.lean#L1)\n", OK),
    ("title form", '[the theorem](A.lean#L3-L4 "lean:beta")\n', OK),
    ("label form refresh", "[`alpha`](A.lean#L9)\n", fix("[`alpha`](A.lean#L1)\n")),
    ("label form added", "[`beta`](A.lean)\n", fix("[`beta`](A.lean#L3-L4)\n")),
    (
        "title form refresh",
        'x [t](A.lean#L1 "lean:beta") y\n',
        fix('x [t](A.lean#L3-L4 "lean:beta") y\n'),
    ),
    ("plain file link", "[A.lean](A.lean) [`A.lean`](A.lean)\n", OK),
    ("ordinary tooltip", '[`alpha`](A.lean "a file")\n', OK),
    ("unknown symbol", "x\n\n[`gamma`](A.lean#L1)\n", reject(3)),
    ("missing file", "[`alpha`](B.lean#L1)\n", reject()),
    ("unmanaged fragment", "[text](A.lean#L1)\n", reject()),
    ("empty lean title", '[t](A.lean#L1 "lean:")\n', reject()),
    ("reference", "[`alpha`][r]\n\n[r]: A.lean#L1\n", reject(3)),
    ("reference title", '[x][r]\n\n[r]: A.lean "lean:alpha"\n', reject(3)),
    ("multiline before url", "[`alpha`](\nA.lean#L1)\n", reject()),
    ("multiline after url", "x\n\n[`alpha`](A.lean#L1\n)\n", reject(3)),
    ("multiline title", '[text](A.lean#L1\n "lean:alpha")\n', reject()),
    (
        "escaped masks multiline",
        "\\[`alpha`](A.lean#L1) [intentionally wrong](\nA.lean#L1)\n",
        reject(),
    ),
    ("query", "[`alpha`](A.lean?view=1#L999)\n", reject()),
    ("entity", "[`alpha`](A.le&#97;n#L999)\n", reject()),
    ("html", '<a href="A.lean#L1">alpha</a>\n', reject()),
    (
        "html data-href first",
        '<a data-href="README.md" href="A.lean#L999">alpha</a>\n',
        reject(),
    ),
    ("html entity", '<a href="A.le&#97;n#L999">alpha</a>\n', reject()),
    ("html comment", '<!-- <a href="A.lean#L999">alpha</a> -->\n', OK),
    ("html file link", '<a data-x="A.lean#L1" href="A.lean">alpha</a>\n', OK),
    ("escaped", "\\[`alpha`](A.lean)\n", OK),
    ("indented code", "para\n\n    [`alpha`](A.lean)\n", OK),
    ("fenced code", "```markdown\n[`alpha`](A.lean#L9)\n```\n", OK),
    ("inline code", "`[`alpha`](A.lean)` and ``[`alpha`](A.lean)``\n", OK),
    (
        "inline code with ]( before stale",
        "`example ](text` and [`alpha`](A.lean#L99)\n",
        fix("`example ](text` and [`alpha`](A.lean#L1)\n"),
    ),
    (
        "inline code with ]( before omitted",
        "`example ](text` and [`alpha`](A.lean)\n",
        fix("`example ](text` and [`alpha`](A.lean#L1)\n"),
    ),
    (
        "table",
        "| a | b |\n| - | - |\n| [`alpha`](A.lean#L2) | [`beta`](A.lean) |\n",
        fix(
            "| a | b |\n| - | - |\n| [`alpha`](A.lean#L1) | [`beta`](A.lean#L3-L4) |\n",
            3,
        ),
    ),
    (
        "table escaped pipe",
        "| a | b |\n| - | - |\n| `x\\|y` [`alpha`](A.lean) | [`alpha`](A.lean) |\n",
        fix(
            "| a | b |\n| - | - |\n"
            "| `x\\|y` [`alpha`](A.lean#L1) | [`alpha`](A.lean#L1) |\n",
            3,
        ),
    ),
    (
        "quoted list",
        "> - item\n>   [`alpha`](A.lean#L7)\n",
        fix("> - item\n>   [`alpha`](A.lean#L1)\n", 2),
    ),
    (
        "literal beside rendered",
        "\\[`alpha`](A.lean) [`alpha`](A.lean)\n",
        fix("\\[`alpha`](A.lean) [`alpha`](A.lean#L1)\n"),
    ),
    (
        "crlf",
        "# T\r\n\r\ntext  \r\n[`alpha`](A.lean#L5) \\[`beta`](A.lean)\r\n\r\n",
        fix("# T\r\n\r\ntext  \r\n[`alpha`](A.lean#L1) \\[`beta`](A.lean)\r\n\r\n", 4),
    ),
]


def run(*args: str) -> tuple[int, str]:
    p = subprocess.run(
        [sys.executable, str(TOOL), *args], capture_output=True, text=True
    )
    return p.returncode, p.stderr


def reports(stderr: str, line: int) -> bool:
    return re.search(rf"README\.md:{line}: ", stderr) is not None


def check_case(root: Path, md: bytes, outcome) -> list[str]:
    readme = root / "README.md"
    readme.write_bytes(md)
    problems = []
    rc, err = run("--check", str(readme))
    if readme.read_bytes() != md:
        problems.append("--check modified the file")
    kind = outcome[0]
    if kind == "ok":
        if rc != 0:
            problems.append(f"--check exited {rc}: {err.strip()}")
        rc, err = run(str(readme))
        if rc != 0 or readme.read_bytes() != md:
            problems.append(f"write exited {rc} or changed {readme.read_bytes()!r}")
    elif kind == "fix":
        _, after, line = outcome
        if rc != 1 or not reports(err, line):
            problems.append(f"--check exited {rc} without line {line}: {err.strip()}")
        rc, err = run(str(readme))
        if rc != 0 or readme.read_bytes() != after.encode():
            problems.append(f"write exited {rc}, left {readme.read_bytes()!r}")
        rc, err = run("--check", str(readme))
        if rc != 0:
            problems.append(f"--check after write exited {rc}: {err.strip()}")
    else:
        _, line = outcome
        if rc != 1 or not reports(err, line):
            problems.append(f"--check exited {rc} without line {line}: {err.strip()}")
        rc, err = run(str(readme))
        if rc != 1 or not reports(err, line) or readme.read_bytes() != md:
            problems.append(f"write exited {rc}, left {readme.read_bytes()!r}")
    return problems


failures = 0
for name, md, outcome in CASES:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "A.lean").write_bytes(LEAN)
        problems = check_case(root, md.encode(), outcome)
    if problems:
        failures += 1
        print(f"FAIL {name}: " + "; ".join(problems), file=sys.stderr)
print(f"{len(CASES) - failures}/{len(CASES)} lean-anchors cases passed")
sys.exit(1 if failures else 0)
