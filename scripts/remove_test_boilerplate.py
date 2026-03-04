#!/usr/bin/env python3
"""Remove duplicated test boilerplate from test files.

Removes local ParseResult* structs, Parse() functions, and helper overloads
that duplicate what's already in fixture_parser.h and helpers_parser_verify.h.
"""

import re
import sys
from pathlib import Path


def find_brace_block(lines: list[str], start: int) -> int:
    """Find the end line index of a brace-balanced block starting at `start`.

    Scans from `start` looking for the first '{', then counts braces
    until balanced. Returns the index of the line containing the closing '}'.
    """
    depth = 0
    found_open = False
    for i in range(start, len(lines)):
        for ch in lines[i]:
            if ch == '{':
                depth += 1
                found_open = True
            elif ch == '}':
                depth -= 1
                if found_open and depth == 0:
                    return i
    return start


def remove_block(lines: list[str], start: int) -> list[str]:
    """Remove lines[start..end] where end is the closing brace of the block."""
    end = find_brace_block(lines, start)
    # Also remove blank line after closing brace if present.
    if end + 1 < len(lines) and lines[end + 1].strip() == '':
        end += 1
    return lines[:start] + lines[end + 1:]


def remove_block_with_preceding_blanks(lines: list[str], start: int) -> list[str]:
    """Remove block and any preceding blank lines."""
    end = find_brace_block(lines, start)
    if end + 1 < len(lines) and lines[end + 1].strip() == '':
        end += 1
    # Remove preceding blank lines.
    while start > 0 and lines[start - 1].strip() == '':
        start -= 1
    return lines[:start] + lines[end + 1:]


def collect_local_parse_result_names(lines: list[str]) -> set[str]:
    """Find all local ParseResult* struct names."""
    names = set()
    for line in lines:
        m = re.match(r'^struct (ParseResult\w+)\s*\{', line)
        if m:
            names.add(m.group(1))
    return names


def is_local_parse_result_struct(line: str) -> str | None:
    """Return the struct name if this line starts a local ParseResult struct."""
    m = re.match(r'^struct (ParseResult\w+)\s*\{', line)
    if m and m.group(1) != 'ParseResult':
        return m.group(1)
    return None


def is_local_parse_function(line: str, local_types: set[str]) -> bool:
    """Check if this line starts a local Parse() function returning a local type."""
    for t in local_types:
        if re.match(rf'^static {t} Parse\(', line):
            return True
    # Also catch 'inline' or no qualifier.
    for t in local_types:
        if re.match(rf'^{t} Parse\(', line):
            return True
    return False


HELPER_PATTERNS = [
    r'^(?:static )?Stmt\* FirstInitialStmt\(',
    r'^(?:static )?Stmt\* FirstInitialBody\(',
    r'^(?:static )?Stmt\* InitialBody\(',
    r'^(?:static )?Expr\* FirstAssignRhs\(',
    r'^(?:static )?Expr\* FirstInitialRHS\(',
    r'^(?:static )?Expr\* FirstInitialExpr\(',
    r'^(?:static )?ModuleItem\* FirstItem\(',
    r'^(?:static )?ModuleItem\* FirstAlwaysItem\(',
    r'^(?:static )?ModuleItem\* FirstAlwaysComb\b',
    r'^(?:static )?ModuleItem\* FirstAlwaysCombItem\(',
    r'^(?:static )?Stmt\* FirstAlwaysCombStmt\(',
    r'^(?:static )?ModuleItem\* FirstFunctionDecl\(',
    r'^(?:static )?ModuleItem\* FirstModuleInst\(',
    r'^(?:static )?ModuleItem\* FindSpecifyBlock\(const std::vector',
    r'^(?:static )?TimingCheckDecl\* GetSoleTimingCheck\(',
    r'^(?:static )?SpecifyItem\* GetSoleSpecifyItem\(',
    r'^(?:static )?SpecifyParseResult ParseSpecifySingle\(',
    r'^(?:static )?ModuleItem\* FirstGenerateIf\(',
]


def is_helper_function(line: str) -> bool:
    """Check if this line starts a duplicated helper function."""
    for pat in HELPER_PATTERNS:
        if re.match(pat, line):
            return True
    return False


def is_local_specify_parse_result(line: str) -> bool:
    """Check if this line starts a local SpecifyParseResult struct."""
    return bool(re.match(r'^struct SpecifyParseResult\s*\{', line))


def process_file(filepath: Path) -> bool:
    """Process a single test file. Returns True if the file was modified."""
    content = filepath.read_text()
    lines = content.split('\n')

    local_types = collect_local_parse_result_names(lines)

    modified = False

    # Multi-pass removal: keep scanning until no more removals.
    changed = True
    while changed:
        changed = False
        i = 0
        while i < len(lines):
            line = lines[i]

            # Remove local ParseResult structs.
            name = is_local_parse_result_struct(line)
            if name:
                lines = remove_block_with_preceding_blanks(lines, i)
                changed = True
                modified = True
                continue

            # Remove local Parse() functions returning local types.
            if is_local_parse_function(line, local_types):
                lines = remove_block_with_preceding_blanks(lines, i)
                changed = True
                modified = True
                continue

            # Remove Parse() that re-defines the fixture's Parse(ParseResult).
            if re.match(r'^static ParseResult Parse\(const std::string', line):
                lines = remove_block_with_preceding_blanks(lines, i)
                changed = True
                modified = True
                continue

            # Remove duplicated helper functions.
            if is_helper_function(line):
                lines = remove_block_with_preceding_blanks(lines, i)
                changed = True
                modified = True
                continue

            # Remove local SpecifyParseResult structs.
            if is_local_specify_parse_result(line):
                lines = remove_block_with_preceding_blanks(lines, i)
                changed = True
                modified = True
                continue

            i += 1

    if not modified:
        return False

    # Replace explicit local type references with ParseResult.
    new_lines = []
    for line in lines:
        new_line = line
        for t in local_types:
            new_line = new_line.replace(t, 'ParseResult')
        new_lines.append(new_line)
    lines = new_lines

    # Add #include "helpers_parser_verify.h" if not present.
    has_helpers_include = any(
        '"helpers_parser_verify.h"' in l for l in lines
    )
    if not has_helpers_include:
        # Insert after the last #include line.
        last_include = -1
        for i, line in enumerate(lines):
            if line.startswith('#include'):
                last_include = i
        if last_include >= 0:
            lines.insert(last_include + 1, '#include "helpers_parser_verify.h"')

    # Clean up: collapse 3+ consecutive blank lines to 2.
    cleaned = []
    blank_count = 0
    for line in lines:
        if line.strip() == '':
            blank_count += 1
            if blank_count <= 2:
                cleaned.append(line)
        else:
            blank_count = 0
            cleaned.append(line)
    lines = cleaned

    # Write back.
    filepath.write_text('\n'.join(lines))
    return True


def main():
    test_dir = Path('test/src/unit')
    lib_test_dir = Path('lib/test')

    files = sorted(test_dir.glob('*.cpp')) + sorted(lib_test_dir.glob('*.cpp'))

    modified_count = 0
    for f in files:
        if process_file(f):
            modified_count += 1
            print(f'  Modified: {f}')

    print(f'\nModified {modified_count} files out of {len(files)} total.')


if __name__ == '__main__':
    main()
