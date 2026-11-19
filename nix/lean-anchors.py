#!/usr/bin/env python3
import re
import sys
from pathlib import Path

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|inductive|structure|class|opaque|axiom)\s+([^\s:({⦃\[]+)"
)
SCOPE_OPEN_RE = re.compile(r"^(namespace|section|mutual)(?:\s+([^\s]+))?\s*$")
SCOPE_END_RE = re.compile(r"^end(?:\s+([^\s]+))?\s*$")
FENCE_RE = re.compile(r"^[ \t>]*(`{3,}|~{3,})")


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
                for p in reversed(split_name(arg)):
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


def scan_links_in_line(line: str):
    i, n = 0, len(line)
    while i < n:
        if line[i] == "`":
            ticks = 1
            while i + ticks < n and line[i + ticks] == "`":
                ticks += 1
            end = line.find("`" * ticks, i + ticks)
            i = n if end == -1 else end + ticks
            continue
        if line[i] == "[" and (i == 0 or line[i - 1] != "!"):
            j = i + 1
            while j < n:
                if line[j] == "`":
                    ticks = 1
                    while j + ticks < n and line[j + ticks] == "`":
                        ticks += 1
                    end = line.find("`" * ticks, j + ticks)
                    if end == -1:
                        j = n
                        break
                    j = end + ticks
                elif line[j] == "\\":
                    j += 2
                elif line[j] == "]":
                    break
                else:
                    j += 1
            if j < n and line[j] == "]" and j + 1 < n and line[j + 1] == "(":
                k = j + 2
                paren = 1
                while k < n and paren > 0:
                    if line[k] == '"':
                        k += 1
                        while k < n:
                            if line[k] == "\\":
                                k += 2
                            elif line[k] == '"':
                                k += 1
                                break
                            else:
                                k += 1
                        continue
                    if line[k] == "(":
                        paren += 1
                    elif line[k] == ")":
                        paren -= 1
                    k += 1
                if paren == 0:
                    yield i, j + 2, k - 1, k, line[i + 1 : j], line[j + 2 : k - 1]
                    i = k
                    continue
        i += 1


DEST_RE = re.compile(r'^\s*(\S+?)(?:\s+"([^"]*)")?\s*$')
CODE_LABEL_RE = re.compile(r"^`([^`\s/]+)`$")


def process_md(
    md_path: Path, cache: dict[Path, list[tuple[list[str], int, int]]], write: bool
) -> list[str]:
    text = md_path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    errors: list[str] = []
    out_lines: list[str] = []
    fence: str | None = None

    for line_no, line in enumerate(lines, 1):
        m_fence = FENCE_RE.match(line)
        if m_fence:
            tok = m_fence.group(1)
            if fence is None:
                fence = tok
            elif tok[0] == fence[0] and len(tok) >= len(fence):
                fence = None
            out_lines.append(line)
            continue
        if fence is not None:
            out_lines.append(line)
            continue

        edits: list[tuple[int, int, str]] = []
        for _, dest_start, dest_end, _, label, dest in scan_links_in_line(line):
            m_dest = DEST_RE.match(dest)
            if not m_dest:
                continue
            url, title = m_dest.group(1), m_dest.group(2)
            if url.startswith(("#", "mailto:")) or "://" in url:
                continue
            rel_path, frag = (url.split("#", 1) + [None])[:2]
            if not rel_path.endswith(".lean"):
                continue
            lean_file = (md_path.parent / rel_path).resolve()
            if not lean_file.is_file():
                errors.append(f"{md_path}:{line_no}: missing file '{rel_path}'")
                continue

            symbol: str | None = None
            if title is not None and title.strip():
                symbol = title.strip()
            else:
                m_lbl = CODE_LABEL_RE.match(label.strip())
                if m_lbl and not m_lbl.group(1).endswith(".lean"):
                    symbol = m_lbl.group(1)

            if symbol is None:
                if frag is not None:
                    errors.append(
                        f"{md_path}:{line_no}: {url}: bare fragment on .lean link; "
                        'use [`symbol`](...) or [text](... "symbol")'
                    )
                continue

            if lean_file not in cache:
                cache[lean_file] = parse_lean_decls(lean_file)
            span, err = resolve_symbol(cache[lean_file], symbol)
            if err is not None or span is None:
                errors.append(f"{md_path}:{line_no}: {rel_path}: {err}")
                continue

            s_ln, e_ln = span
            want_frag = f"L{s_ln}" if s_ln == e_ln else f"L{s_ln}-L{e_ln}"
            new_url = f"{rel_path}#{want_frag}"
            new_dest = f'{new_url} "{title}"' if title is not None else new_url
            if dest != new_dest:
                if write:
                    edits.append((dest_start, dest_end, new_dest))
                else:
                    errors.append(
                        f"{md_path}:{line_no}: {url} -> expected {new_url} for '{symbol}'"
                    )

        if edits:
            rebuilt = []
            prev = 0
            for s, e, rep in edits:
                rebuilt.append(line[prev:s])
                rebuilt.append(rep)
                prev = e
            rebuilt.append(line[prev:])
            out_lines.append("".join(rebuilt))
        else:
            out_lines.append(line)

    if write and not errors:
        new_text = "".join(out_lines)
        if new_text != text:
            md_path.write_text(new_text, encoding="utf-8")
    return errors


def collect_md_files(paths: list[str]) -> list[Path]:
    files: list[Path] = []
    for raw in paths:
        p = Path(raw)
        if p.is_dir():
            files.extend(
                sorted(
                    f
                    for f in p.rglob("*.md")
                    if not any(part.startswith(".") for part in f.relative_to(p).parts)
                )
            )
        elif p.suffix == ".md":
            files.append(p)
    return files


def main(argv: list[str]) -> int:
    check_only = False
    args = argv[1:]
    if args and args[0] == "--check":
        check_only = True
        args = args[1:]
    cache: dict[Path, list[tuple[list[str], int, int]]] = {}
    errors: list[str] = []
    for md in collect_md_files(args):
        errors.extend(process_md(md, cache, write=not check_only))
    if errors:
        for err in errors:
            print(err, file=sys.stderr)
        print(f"{len(errors)} Lean anchor error(s).", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
