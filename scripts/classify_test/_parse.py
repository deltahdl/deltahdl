"""Source-file parsing helpers for classify_test (stage 1)."""

import re
from pathlib import Path

from ._models import ParsedFile, PreambleItem, TestBlock


def _update_brace_depth(
    line: str,
    depth: int,
    in_string: bool,
    in_block_comment: bool,
) -> tuple[int, bool, bool, bool]:
    """Scan one line, updating brace depth and lexer state.

    Returns (depth, in_string, in_block_comment, found_close).
    """
    j = 0
    while j < len(line):
        ch = line[j]
        if in_block_comment:
            if ch == "*" and j + 1 < len(line) and line[j + 1] == "/":
                in_block_comment = False
                j += 1
        elif in_string:
            if ch == "\\":
                j += 1
            elif ch == '"':
                in_string = False
        elif ch == "/" and j + 1 < len(line) and line[j + 1] in "/*":
            if line[j + 1] == "/":
                break
            in_block_comment = True
            j += 1
        elif ch == '"':
            in_string = True
        elif ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return depth, in_string, in_block_comment, True
        j += 1
    return depth, in_string, in_block_comment, False


def extract_brace_block(
    lines: list[str], start_idx: int,
) -> tuple[list[str], int]:
    """Extract a brace-delimited block starting from start_idx."""
    depth, in_string, in_block_comment = 0, False, False
    block: list[str] = []
    for i in range(start_idx, len(lines)):
        block.append(lines[i])
        depth, in_string, in_block_comment, found = _update_brace_depth(
            lines[i], depth, in_string, in_block_comment,
        )
        if found:
            return block, i
    raise ValueError(
        f"Unmatched brace starting at line {start_idx + 1}",
    )


def is_section_header(line: str) -> bool:
    """Check if a line is a section separator (=== or --- banners)."""
    stripped = line.strip()
    if stripped.startswith("//"):
        content = stripped[2:].strip()
        if len(content) >= 10 and (
            all(c == "=" for c in content)
            or all(c == "-" for c in content)
        ):
            return True
    return False


def _parse_header(
    lines: list[str],
) -> tuple[list[str], str | None, bool, int]:
    """Parse file header: includes, using-line, namespace wrapper.

    Returns (includes, using_line, has_namespace, body_start_idx).
    """
    includes: list[str] = []
    using_line: str | None = None
    has_ns = False
    i = 0

    while i < len(lines) and not lines[i].strip().startswith("#include"):
        i += 1

    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("#include"):
            includes.append(lines[i].rstrip("\n"))
            i += 1
            continue
        if stripped != "":
            break
        i += 1

    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("using namespace"):
            using_line = lines[i].rstrip("\n")
            i += 1
            break
        if stripped != "":
            break
        i += 1  # pragma: no cover — unreachable (second loop consumes blanks)

    while i < len(lines) and lines[i].strip() == "":
        i += 1

    if i < len(lines) and lines[i].strip() == "namespace {":
        has_ns = True
        i += 1

    return includes, using_line, has_ns, i


def _try_parse_preamble(
    lines: list[str],
    i: int,
    stripped: str,
    comments: list[str],
) -> tuple[PreambleItem | None, int]:
    """Try to parse a preamble item (brace block or declaration).

    Mutates *comments* in place (clears on consumption).
    Returns (PreambleItem | None, new_i).
    """
    if "{" in stripped:
        try:
            blk, end = extract_brace_block(lines, i)
            item_lines = [ln.rstrip("\n") for ln in blk]
            if comments:
                item_lines = list(comments) + item_lines
                comments.clear()
            return PreambleItem(lines=item_lines), end + 1
        except ValueError:
            pass
    if stripped.endswith(";"):
        decl = list(comments) + [lines[i].rstrip("\n")]
        comments.clear()
        return PreambleItem(lines=decl), i + 1
    comments.append(lines[i].rstrip("\n"))
    return None, i + 1


def _parse_body(
    lines: list[str], start_idx: int,
) -> tuple[list[PreambleItem], list[PreambleItem], list[TestBlock], bool]:
    """Parse body: extract TEST blocks and preamble items.

    Returns (global_preamble, all_tests, found_namespace).
    """
    g_pre: list[PreambleItem] = []
    all_tests: list[TestBlock] = []
    has_ns = False
    comments: list[str] = []
    in_global = True
    s_pre: list[PreambleItem] = []
    i = start_idx

    while i < len(lines):
        stripped = lines[i].strip()
        if stripped == "" or re.match(
            r'^\}\s*//\s*namespace(\s+\w+)?$', stripped,
        ):
            i += 1
            continue
        if stripped.startswith("//"):
            comments.append(lines[i].rstrip("\n"))
            i += 1
            continue
        if re.match(r'^namespace(\s+\w+)?\s*\{$', stripped):
            has_ns = True
            i += 1
            continue
        m = re.match(r"^TEST(?:_[FP])?\((\w+),\s*(\w+)\)", stripped)
        if not m and i + 1 < len(lines):
            m = re.match(
                r"^TEST(?:_[FP])?\((\w+),\s*(\w+)\)",
                stripped.rstrip() + " " + lines[i + 1].strip(),
            )
        if m:
            in_global = False
            blk, end = extract_brace_block(lines, i)
            all_tests.append(TestBlock(
                suite_name=m.group(1),
                test_name=m.group(2),
                lines=[ln.rstrip("\n") for ln in blk],
                preceding_comments=list(comments),
            ))
            comments.clear()
            i = end + 1
            continue
        item, i = _try_parse_preamble(
            lines, i, stripped, comments,
        )
        if item:
            target = g_pre if in_global else s_pre
            target.append(item)
    return g_pre, s_pre, all_tests, has_ns


def parse_file(filepath: Path) -> ParsedFile:
    """Parse a standalone test file into structured components."""
    text = filepath.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    includes, using_line, hdr_ns, body_start = _parse_header(lines)
    g_pre, s_pre, all_tests, body_ns = _parse_body(lines, body_start)
    return ParsedFile(
        includes=includes,
        using_line=using_line,
        has_namespace_wrapper=hdr_ns or body_ns,
        global_preamble=g_pre,
        section_preamble=s_pre,
        all_tests=all_tests,
        source_filename=filepath.name,
    )
