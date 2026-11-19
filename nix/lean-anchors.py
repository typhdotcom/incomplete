#!/usr/bin/env python3
from html.parser import HTMLParser
import os
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

from markdown_it import MarkdownIt
from markdown_it.rules_inline.link import link as link_rule

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|inductive|structure|class|opaque|axiom)\s+([^\s:({⦃\[]+)"
)
SCOPE_OPEN_RE = re.compile(r"^(namespace|section|mutual)(?:\s+([^\s]+))?\s*$")
SCOPE_END_RE = re.compile(r"^end(?:\s+([^\s]+))?\s*$")
TITLE_PREFIX = "lean:"
USAGE_HINT = 'use single-line [`symbol`](path.lean) or [text](path.lean "lean:symbol")'
MANAGED_URL_RE = re.compile(r"^([^\s#?%&\\<>()]+\.lean)(?:#[A-Za-z0-9-]*)?$")
SYMBOL_RE = re.compile(r"^[^\s`/]+$")
NEWLINE_RE = re.compile(r"\r\n?|\n")


def clean_part(part: str) -> str:
    return part.removeprefix("«").removesuffix("»")


def split_name(name: str) -> list[str]:
    return [clean_part(p) for p in name.split(".") if p]


def strip_comments(src: str) -> str:
    out: list[str] = []
    i, n, block = 0, len(src), 0
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if block > 0:
            if ch == "/" and nxt == "-":
                block += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif ch == "/" and nxt == "-":
            block = 1
            out.append("  ")
            i += 2
        elif ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif ch == '"':
            out.append(ch)
            i += 1
            while i < n:
                c = src[i]
                out.append(c)
                i += 1
                if c == "\\" and i < n:
                    out.append(src[i])
                    i += 1
                elif c == '"':
                    break
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def sig_end_line(lines: list[str], start_idx: int, name_end_col: int) -> int:
    depth = 0
    last_nonblank = start_idx
    for idx in range(start_idx, len(lines)):
        line = lines[idx]
        col = name_end_col if idx == start_idx else 0
        if idx > start_idx and depth == 0:
            stripped = line.lstrip(" ")
            if not stripped:
                return last_nonblank + 1
            if len(line) == len(stripped) or stripped.startswith("|"):
                return last_nonblank + 1
        if line.strip():
            last_nonblank = idx
        i, n = col, len(line)
        while i < n:
            ch = line[i]
            if ch == '"':
                i += 1
                while i < n:
                    if line[i] == "\\":
                        i += 2
                    elif line[i] == '"':
                        i += 1
                        break
                    else:
                        i += 1
                continue
            if ch in "([{⦃":
                depth += 1
            elif ch in ")]}⦄":
                depth = max(0, depth - 1)
            elif depth == 0:
                if line.startswith(":=", i):
                    return idx + 1
                if (
                    line.startswith("where", i)
                    and (i == 0 or not (line[i - 1].isalnum() or line[i - 1] == "_"))
                    and (
                        i + 5 == n or not (line[i + 5].isalnum() or line[i + 5] == "_")
                    )
                ):
                    return idx + 1
            i += 1
    return last_nonblank + 1


def parse_lean_decls(lean_path: Path) -> list[tuple[list[str], int, int]]:
    clean = strip_comments(lean_path.read_text(encoding="utf-8"))
    lines = clean.splitlines()
    scopes: list[tuple[str, list[str]]] = []
    decls: list[tuple[list[str], int, int]] = []

    for idx, raw in enumerate(lines):
        s = raw.strip()
        if not s:
            continue
        m_open = SCOPE_OPEN_RE.match(s)
        if m_open and len(raw) == len(raw.lstrip(" ")):
            kind, arg = m_open.group(1), m_open.group(2)
            parts = split_name(arg) if arg else []
            if kind == "namespace":
                for p in parts:
                    scopes.append(("ns", [p]))
            elif kind == "section":
                scopes.append(("sec", parts))
            else:
                scopes.append(("mut", []))
            continue
        m_end = SCOPE_END_RE.match(s)
        if m_end and len(raw) == len(raw.lstrip(" ")):
            arg = m_end.group(1)
            if not arg:
                if scopes:
                    scopes.pop()
            else:
                for _ in split_name(arg):
                    if scopes:
                        scopes.pop()
            continue
        m_decl = DECL_RE.match(raw)
        if m_decl:
            raw_name = m_decl.group(2)
            parts = split_name(raw_name)
            if parts and parts[0] == "_root_":
                full_parts = parts[1:]
            else:
                ns_prefix = [p for kind, ps in scopes if kind == "ns" for p in ps]
                full_parts = ns_prefix + parts
            end_ln = sig_end_line(lines, idx, m_decl.end(2))
            decls.append((full_parts, idx + 1, end_ln))
    return decls


def resolve_symbol(
    decls: list[tuple[list[str], int, int]], symbol: str
) -> tuple[tuple[int, int] | None, str | None]:
    want = split_name(symbol)
    if not want:
        return None, "empty Lean symbol"
    exact = [(s, e) for parts, s, e in decls if parts == want]
    if len(exact) == 1:
        return exact[0], None
    k = len(want)
    suffix = [
        (parts, s, e) for parts, s, e in decls if len(parts) >= k and parts[-k:] == want
    ]
    spans = sorted({(s, e) for _, s, e in suffix})
    if len(spans) == 1:
        return spans[0], None
    if not spans:
        return None, f"symbol '{symbol}' not found"
    names = ", ".join(".".join(parts) for parts, _, _ in suffix)
    return None, f"symbol '{symbol}' is ambiguous ({names})"


def lean_target(href: str):
    if not href or href.startswith("#"):
        return None
    parts = urlsplit(href)
    if parts.scheme or parts.netloc or not unquote(parts.path).endswith(".lean"):
        return None
    return parts


def located_link(state, silent: bool) -> bool:
    start, first = state.pos, len(state.tokens)
    if not link_rule(state, silent):
        return False
    if not silent:
        end, src = state.pos, state.src
        opener = next(t for t in state.tokens[first:] if t.type == "link_open")
        dest = None
        p = state.md.helpers.parseLinkLabel(state, start, True) + 1
        if end > p and src[p] == "(":
            p += 1
            while p < end and src[p] in " \t\n":
                p += 1
            res = state.md.helpers.parseLinkDestination(src, p, end)
            if res.ok:
                dest = (p, res.pos)
        opener.meta["span"] = (start, end)
        opener.meta["dest"] = dest
    return True


def make_parser() -> MarkdownIt:
    md = MarkdownIt("commonmark").enable(["table", "strikethrough"])
    md.inline.ruler.at("link", located_link)
    return md


def align(content: str, line: str, base: int, cursor: int) -> list[int] | None:
    # Inline content is its source line minus container prefixes and cell
    # delimiters; table cells also drop the backslash of `\|`.
    for start in range(cursor, len(line) - len(content) + 1):
        out, j = [], start
        for ch in content:
            if j < len(line) and line[j] == ch:
                out.append(base + j)
                j += 1
            elif ch == "|" and line.startswith("\\|", j):
                out.append(base + j + 1)
                j += 2
            else:
                break
        else:
            return out
    return None


class AnchorHrefs(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.hrefs: list[str] = []

    def handle_starttag(self, tag, attrs) -> None:
        if tag == "a":
            self.hrefs.extend(v or "" for k, v in attrs if k == "href")

    handle_startendtag = handle_starttag


def process_md(
    md_path: Path, cache: dict[Path, list[tuple[list[str], int, int]]], write: bool
) -> list[str]:
    with open(md_path, encoding="utf-8", newline="") as f:
        text = f.read()
    errors: list[str] = []
    edits: list[tuple[int, int, str]] = []

    # markdown-it numbers lines after normalizing every line ending to \n.
    line_spans, pos = [], 0
    for m in NEWLINE_RE.finditer(text):
        line_spans.append((pos, m.start()))
        pos = m.end()
    line_spans.append((pos, len(text)))
    cursors: dict[int, int] = {}

    def err(line: int, href: str, msg: str) -> None:
        errors.append(f"{md_path}:{line}: {href}: {msg}")

    md = make_parser()
    env: dict = {}
    tokens = md.parse(text, env)

    def_hrefs: set[str] = set()
    for label, ref in env.get("references", {}).items():
        href = ref.get("href", "")
        title = ref.get("title") or ""
        if lean_target(href) and ("#" in href or title.startswith(TITLE_PREFIX)):
            def_hrefs.add(href)
            err(
                (ref.get("map") or [0])[0] + 1,
                f"[{label}]: {href}",
                f"reference-style Lean symbol/line links are unsupported; {USAGE_HINT}",
            )

    def check_html(content: str, line: int) -> None:
        parser = AnchorHrefs()
        parser.feed(content)
        parser.close()
        for href in parser.hrefs:
            if lean_target(href) and "#" in href:
                err(
                    line,
                    href,
                    f"HTML <a> Lean line links are unsupported; {USAGE_HINT}",
                )

    def locate(tok) -> list[list[int] | None]:
        out = []
        for i, cline in enumerate(tok.content.split("\n")):
            ln = tok.map[0] + i if tok.map else -1
            if not 0 <= ln < len(line_spans):
                out.append(None)
                continue
            s, e = line_spans[ln]
            cur = cursors.get(ln, 0)
            offs = align(cline, text[s:e], s, cur) if cur >= 0 else None
            if offs is None:
                cursors[ln] = -1
            elif offs:
                cursors[ln] = offs[-1] + 1 - s
            out.append(offs)
        return out

    def check_link(tok, children, i: int, offsets) -> None:
        opener = children[i]
        href = opener.attrGet("href") or ""
        title = opener.attrGet("title")
        if lean_target(href) is None:
            return
        content = tok.content
        ls, le = opener.meta.get("span", (0, 0))
        li = content.count("\n", 0, ls)
        col = ls - (content.rfind("\n", 0, ls) + 1)
        line = (tok.map[0] if tok.map else 0) + li + 1
        close = next(
            (
                j
                for j in range(i + 1, len(children))
                if children[j].type == "link_close"
            ),
            len(children),
        )
        label = children[i + 1 : close]

        symbol: str | None = None
        if title is not None:
            if title.startswith(TITLE_PREFIX):
                symbol = title[len(TITLE_PREFIX) :].strip()
                if not symbol:
                    err(
                        line, href, f"empty symbol after '{TITLE_PREFIX}'; {USAGE_HINT}"
                    )
                    return
        elif (
            len(label) == 1
            and label[0].type == "code_inline"
            and SYMBOL_RE.match(label[0].content)
            and not label[0].content.endswith(".lean")
        ):
            symbol = label[0].content
        if symbol is None:
            if "#" in href:
                err(line, href, f"unmanaged fragment on .lean link; {USAGE_HINT}")
            return

        dest = opener.meta.get("dest")
        if dest is None:
            if href not in def_hrefs:
                err(line, href, f"reference-style Lean symbol/line link; {USAGE_HINT}")
            return
        if "\n" in content[ls:le]:
            err(line, href, f"multiline Lean symbol/line link; {USAGE_HINT}")
            return
        line_offs = offsets[li]
        ds, de = dest
        if line_offs is None:
            err(line, href, "cannot locate this link in the source; " + USAGE_HINT)
            return
        d0 = col + (ds - ls)
        s, e = line_offs[d0], line_offs[d0 + (de - ds) - 1] + 1
        raw = text[s:e]
        if raw != content[ds:de]:
            err(line, href, "cannot locate this link in the source; " + USAGE_HINT)
            return
        m_url = MANAGED_URL_RE.match(raw)
        if m_url is None:
            err(line, href, f"unsupported Lean symbol/line link; {USAGE_HINT}")
            return

        rel_path = m_url.group(1)
        lean_file = (md_path.parent / rel_path).resolve()
        if not lean_file.is_file():
            errors.append(f"{md_path}:{line}: missing file '{rel_path}'")
            return
        if lean_file not in cache:
            cache[lean_file] = parse_lean_decls(lean_file)
        span, why = resolve_symbol(cache[lean_file], symbol)
        if why is not None or span is None:
            errors.append(f"{md_path}:{line}: {rel_path}: {why}")
            return
        s_ln, e_ln = span
        want = f"{rel_path}#L{s_ln}" + ("" if s_ln == e_ln else f"-L{e_ln}")
        if raw == want:
            return
        if write:
            edits.append((s, e, want))
        else:
            err(line, raw, f"expected {want} for '{symbol}'")

    for tok in tokens:
        line = tok.map[0] + 1 if tok.map else 1
        if tok.type == "html_block":
            check_html(tok.content, line)
        if tok.type != "inline" or not tok.children:
            continue
        offsets = locate(tok)
        for i, child in enumerate(tok.children):
            if child.type == "html_inline":
                check_html(child.content, line)
            elif child.type == "link_open":
                check_link(tok, tok.children, i, offsets)

    if write and not errors and edits:
        out, prev = [], 0
        for s, e, rep in sorted(edits):
            out += [text[prev:s], rep]
            prev = e
        out.append(text[prev:])
        with open(md_path, "w", encoding="utf-8", newline="") as f:
            f.write("".join(out))
    return errors


def collect_md_files(paths: list[str]) -> list[Path]:
    files: list[Path] = []
    seen: set[Path] = set()

    def add(p: Path) -> None:
        rp = p.resolve()
        if not p.is_symlink() and rp not in seen:
            seen.add(rp)
            files.append(p)

    for raw in paths:
        p = Path(raw)
        if p.is_symlink():
            continue
        if p.is_dir():
            for dirpath, dirnames, filenames in os.walk(p, followlinks=False):
                dirnames[:] = sorted(d for d in dirnames if not d.startswith("."))
                for fn in sorted(filenames):
                    if fn.endswith(".md"):
                        add(Path(dirpath) / fn)
        elif p.is_file() and p.suffix == ".md":
            add(p)
    return files


def main(argv: list[str]) -> int:
    args = argv[1:]
    check_only = bool(args) and args[0] == "--check"
    if check_only:
        args = args[1:]
    cache: dict[Path, list[tuple[list[str], int, int]]] = {}
    errors: list[str] = []
    for md in collect_md_files(args):
        errors.extend(process_md(md, cache, write=not check_only))
    if errors:
        for e in errors:
            print(e, file=sys.stderr)
        print(f"{len(errors)} Lean anchor error(s).", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
