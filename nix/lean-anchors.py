#!/usr/bin/env python3
from html.parser import HTMLParser
import os
import re
import secrets
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

from markdown_it import MarkdownIt
from markdown_it.common.utils import unescapeAll

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


def is_ascii_punct(ch: str) -> bool:
    return ch.isascii() and not ch.isalnum() and ch.isprintable() and not ch.isspace()


def inline_destinations(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    last = 0
    for m in re.finditer(r"\]\(", text):
        i, n = m.end(), len(text)
        while i < n and text[i] in " \t":
            i += 1
        if i < last or i >= n or text[i] in "<\n":
            continue
        j, depth = i, 0
        while j < n:
            ch = text[j]
            if ch == "\\" and j + 1 < n and is_ascii_punct(text[j + 1]):
                j += 2
                continue
            if ch.isspace() or ord(ch) < 0x20:
                break
            if ch == "(":
                depth += 1
            elif ch == ")":
                if depth == 0:
                    break
                depth -= 1
            j += 1
        if depth == 0 and j > i:
            spans.append((i, j))
            last = j
    return spans


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
    text = md_path.read_text(encoding="utf-8")
    errors: list[str] = []
    edits: list[tuple[int, int, str]] = []

    def line_of(offset: int) -> int:
        return text.count("\n", 0, offset) + 1

    def err(line: int, href: str, msg: str) -> None:
        errors.append(f"{md_path}:{line}: {href}: {msg}")

    # Each inline destination is swapped for a unique probe, so the parse
    # itself says which source spans render as links; literal text keeps its probe.
    spans = inline_destinations(text)
    tag = f"lean-anchor-{secrets.token_hex(8)}-"
    probe_parts, prev = [], 0
    for idx, (s, e) in enumerate(spans):
        probe_parts += [text[prev:s], f"{tag}{idx}"]
        prev = e
    probe_parts.append(text[prev:])
    probe = "".join(probe_parts)
    probe_re = re.compile(re.escape(tag) + r"(\d+)")

    def unprobe(s: str) -> str:
        return probe_re.sub(lambda m: text[slice(*spans[int(m.group(1))])], s)

    md = MarkdownIt("commonmark").enable(["table", "strikethrough"])
    env: dict = {}
    tokens = md.parse(probe, env)

    def_hrefs: set[str] = set()
    for label, ref in env.get("references", {}).items():
        href = unprobe(ref.get("href", ""))
        title = ref.get("title") or ""
        target = lean_target(href)
        if target and ("#" in href or title.startswith(TITLE_PREFIX)):
            def_hrefs.add(href)
            err(
                (ref.get("map") or [0])[0] + 1,
                f"[{label}]: {href}",
                f"reference-style Lean symbol/line links are unsupported; {USAGE_HINT}",
            )

    def check_html(content: str, line: int) -> None:
        parser = AnchorHrefs()
        parser.feed(unprobe(content))
        parser.close()
        for href in parser.hrefs:
            if lean_target(href) and "#" in href:
                err(
                    line,
                    href,
                    f"HTML <a> Lean line links are unsupported; {USAGE_HINT}",
                )

    def check_link(children, i: int, block_line: int) -> None:
        tok = children[i]
        href = tok.attrGet("href") or ""
        title = tok.attrGet("title")
        m_probe = probe_re.fullmatch(href)
        if m_probe:
            s, e = spans[int(m_probe.group(1))]
            raw: str | None = text[s:e]
            href = md.normalizeLink(unescapeAll(raw))
            line = line_of(s)
        else:
            raw, line = None, block_line
        if lean_target(href) is None:
            return
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

        m_url = MANAGED_URL_RE.match(raw) if raw is not None else None
        if m_url is None:
            if raw is None and href in def_hrefs:
                return
            kind = "reference-style" if raw is None else "unsupported"
            err(line, href, f"{kind} Lean symbol/line link; {USAGE_HINT}")
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

    def walk(toks, block_line: int = 1) -> None:
        for tok in toks:
            line = tok.map[0] + 1 if tok.map else block_line
            if tok.type in ("html_block", "html_inline"):
                check_html(tok.content, line)
            if tok.children:
                for i, child in enumerate(tok.children):
                    if child.type == "html_inline":
                        check_html(child.content, line)
                    elif child.type == "link_open":
                        check_link(tok.children, i, line)

    walk(tokens)

    if write and not errors and edits:
        out, prev = [], 0
        for s, e, rep in sorted(edits):
            out += [text[prev:s], rep]
            prev = e
        out.append(text[prev:])
        md_path.write_text("".join(out), encoding="utf-8")
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
