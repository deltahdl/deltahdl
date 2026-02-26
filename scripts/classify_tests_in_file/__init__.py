#!/usr/bin/env python3
"""Classify tests in a file into per-LRM-clause files.

Usage:
  python3 scripts/classify_tests_in_file.py \
    --file path/to/test.cpp --output-dir path/to/out
  python3 scripts/classify_tests_in_file.py \
    --file path/to/test.cpp --output-dir path/to/out --dry-run
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
import textwrap
from dataclasses import dataclass
from pathlib import Path

from ._split import (
    _batch_tests,
    _count_file_lines,
    _dedup_preamble,
    _find_namespace_close,
    _flush_overflow,
    _next_suffix_file,
    _rename_base_to_suffix,
    _render_tests,
    _split_tests,
    _test_line_count,
    _write_one_file,
    _write_overflow_file,
    append_tests_to_file,
    strip_lrm_quotes,
)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class TestBlock:
    """A single TEST/TEST_F/TEST_P block with classification metadata."""

    suite_name: str
    test_name: str
    lines: list[str]
    preceding_comments: list[str]
    prefix: str | None = None
    clause: str | None = None
    rationale: str | None = None


@dataclass
class PreambleItem:
    """A preamble declaration (struct, enum, helper function, etc.)."""

    lines: list[str]


@dataclass
class ParsedFile:
    """Result of parsing a standalone test file."""

    includes: list[str]
    using_line: str | None
    has_namespace_wrapper: bool
    global_preamble: list[PreambleItem]
    section_preamble: list[PreambleItem]
    all_tests: list[TestBlock]
    source_filename: str | None = None


_VALID_PREFIXES = frozenset({
    "test_preprocessor_",
    "test_lexer_",
    "test_parser_",
    "test_elaborator_",
    "test_simulator_",
    "test_synthesizer_",
    "test_non_lrm_",
})

_CLAUSE_RE = re.compile(
    r"^(?:non[-_]lrm|[A-Z](?:\.\d+)*|\d+(?:\.\d+)*)$",
)


# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

def find_repo_root() -> Path:
    """Find repo root by walking up from CWD looking for test/CMakeLists.txt."""
    d = Path.cwd().resolve()
    while True:
        if (d / "test" / "CMakeLists.txt").exists():
            return d
        parent = d.parent
        if parent == d:
            print("ERROR: Cannot find repo root")
            sys.exit(1)
        d = parent


REPO_ROOT = find_repo_root()
CMAKE_PATH = REPO_ROOT / "test" / "CMakeLists.txt"


# ---------------------------------------------------------------------------
# Stage 1: Parse — brace extraction
# ---------------------------------------------------------------------------

def _update_brace_depth(line, depth, in_string, in_block_comment):
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


def extract_brace_block(lines, start_idx):
    """Extract a brace-delimited block starting from start_idx."""
    depth, in_string, in_block_comment = 0, False, False
    block = []
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


# ---------------------------------------------------------------------------
# Stage 1: Parse — helpers
# ---------------------------------------------------------------------------

def is_section_header(line):
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


def _parse_header(lines):
    """Parse file header: includes, using-line, namespace wrapper.

    Returns (includes, using_line, has_namespace, body_start_idx).
    """
    includes = []
    using_line = None
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


def _try_parse_preamble(lines, i, stripped, comments):
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


def _parse_body(lines, start_idx):
    """Parse body: extract TEST blocks and preamble items.

    Returns (global_preamble, all_tests, found_namespace).
    """
    g_pre = []
    all_tests = []
    has_ns = False
    comments = []
    in_global = True
    s_pre = []
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


def parse_file(filepath):
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


# ---------------------------------------------------------------------------
# Stage 2: Classify via Claude
# ---------------------------------------------------------------------------

def existing_non_lrm_topics(test_dir):
    """Scan output dir for existing test_non_lrm_*.cpp topic names."""
    topics = set()
    pattern = str(test_dir / "test_non_lrm_*.cpp")
    for fpath in sorted(glob.glob(pattern)):
        stem = Path(fpath).stem
        topic = stem[len("test_non_lrm_"):]
        if len(topic) >= 2 and topic[-2] == "_" and topic[-1].isalpha():
            topic = topic[:-2]
        if topic:
            topics.add(topic)
    return sorted(topics)


_PROMPT_TEMPLATE = """Classify this test. Determine:

1. PREFIX — which pipeline stage the test exercises. Use EXACTLY one of:
   - test_preprocessor_
   - test_lexer_
   - test_parser_
   - test_elaborator_
   - test_simulator_
   - test_synthesizer_
   - test_non_lrm_
   Read the project architecture document for what each stage covers.
   Do NOT invent new prefixes.

2. CLAUSE — which IEEE 1800-2023 clause the test covers based on what
   the code actually DOES. Ignore source comments — they may be wrong.
   Use the most specific subclause possible (e.g. 9.2.2.2.2, not 9.2).
   Clauses and annexes can be arbitrarily deep — use the most specific
   one that applies. Read the LRM to find the right depth.
   Read the relevant LRM sections to verify — do not guess from titles.
   If no LRM clause applies: non-lrm

3. NON_LRM_TOPIC — only when clause is "non-lrm". A short snake_case
   topic (e.g. "aig", "arena", "dpi_helpers"). Set to null otherwise.

4. RATIONALE — describe the process you followed to reach your
   conclusion. Specifically:
   - Which LRM sections did you Read (use the Read tool) and why?
   - What did those sections contain that confirmed or ruled them out?
   - If you concluded non-lrm, explain which sections you checked
     and why none of them apply.
   Do NOT just state the conclusion — show your work.
{topics}
Project architecture: {arch_path}
IEEE 1800-2023 LRM: {lrm_path}
{file_context}
TEST({suite}, {test_name}):
{test_body}

Respond with ONLY JSON:
{{"prefix": "...", "clause": "...", "non_lrm_topic": ..., "rationale": "..."}}
"""


def _build_prompt(test, parsed, test_dir, lrm_path, arch_path):
    """Build the Claude classification prompt for a single test."""
    topics = existing_non_lrm_topics(test_dir)
    topics_hint = ""
    if topics:
        topics_hint = (
            "   Existing non-lrm topic files: "
            + ", ".join(topics)
            + "\n   PREFER reusing one of these topics when the"
            " test fits, to avoid near-duplicate filenames.\n"
        )
    context_parts = []
    if parsed.source_filename:
        context_parts.append(f"Source file: {parsed.source_filename}")
    if parsed.includes:
        context_parts.append("Includes:\n" + "\n".join(parsed.includes))
    all_preamble = list(parsed.global_preamble) + list(parsed.section_preamble)
    if all_preamble:
        preamble_lines = []
        for item in all_preamble:
            preamble_lines.extend(item.lines)
        context_parts.append(
            "Helper definitions:\n" + "\n".join(preamble_lines),
        )
    file_context = ""
    if context_parts:
        file_context = (
            "FILE CONTEXT:\n" + "\n\n".join(context_parts) + "\n"
        )
    body = "\n".join(test.preceding_comments + test.lines)
    return _PROMPT_TEMPLATE.format(
        topics=topics_hint,
        arch_path=arch_path,
        lrm_path=lrm_path,
        file_context=file_context,
        suite=test.suite_name,
        test_name=test.test_name,
        test_body=body,
    )


def _extract_json(text):
    """Extract a JSON object from Claude's response text."""
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass
    start = text.find("{")
    end = text.rfind("}") + 1
    if 0 <= start < end:
        try:
            return json.loads(text[start:end])
        except json.JSONDecodeError:
            pass
    print(f"ERROR: Could not parse JSON:\n{text[:500]}")
    sys.exit(1)


def _call_claude(prompt):
    """Call Claude CLI and return parsed JSON response."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    result = subprocess.run(
        ["claude", "-p", "--model", "sonnet", "--output-format", "json",
         "--allowedTools", "Read"],
        input=prompt,
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Claude CLI failed (RC={result.returncode}):"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    raw = result.stdout.strip()
    # --output-format json wraps Claude's text in an envelope
    # with keys like "result", "session_id", etc.
    try:
        envelope = json.loads(raw)
    except json.JSONDecodeError:
        return _extract_json(raw)
    if isinstance(envelope, dict) and "result" in envelope:
        return _extract_json(envelope["result"])
    return _extract_json(raw)


def _validate_response(response, test_name):
    """Validate Claude's classification response or exit with error."""
    missing = [k for k in ("prefix", "clause") if k not in response]
    if missing:
        print(f"ERROR: Classification for test {test_name} is missing"
              f" required key(s): {', '.join(missing)}")
        sys.exit(1)
    prefix = response["prefix"]
    if prefix not in _VALID_PREFIXES:
        print(f'ERROR: Invalid prefix "{prefix}" for test {test_name}.'
              f"\n  Valid: {', '.join(sorted(_VALID_PREFIXES))}")
        sys.exit(1)
    clause = response["clause"]
    if not _CLAUSE_RE.match(clause):
        print(f'ERROR: Invalid clause "{clause}" for test {test_name}.'
              "\n  Expected: numeric (6.1.2), annex (A.6.3),"
              " or non-lrm")
        sys.exit(1)
    is_non_lrm = clause.replace("_", "-") == "non-lrm"
    if is_non_lrm and not response.get("non_lrm_topic"):
        print(f"ERROR: Classification for test {test_name} has clause"
              f' "{clause}" but no non_lrm_topic.'
              "\n  A topic is required to avoid the misc bucket.")
        sys.exit(1)


def _apply_classification(test, response):
    """Apply a single classification result to a test block."""
    _validate_response(response, test.test_name)
    test.prefix = response["prefix"]
    clause = response["clause"]
    if clause.replace("_", "-") == "non-lrm":
        clause = "non-lrm"
    topic = response.get("non_lrm_topic")
    if clause == "non-lrm" and topic:
        clause = f"non-lrm:{topic}"
    test.clause = clause
    test.rationale = response.get("rationale", "")


def classify_tests(tests, parsed, test_dir, lrm_path, arch_path):
    """Use Claude to classify each test's prefix and clause."""
    for test in tests:
        prompt = _build_prompt(
            test, parsed, test_dir, lrm_path, arch_path,
        )
        response = _call_claude(prompt)
        _apply_classification(test, response)
    return tests


# ---------------------------------------------------------------------------
# Stage 3: Deduplicate
# ---------------------------------------------------------------------------

def find_existing_tests(target_base, test_dir, exclude_path=None):
    """Find TEST names in existing clause files matching target_base."""
    existing_names = set()
    patterns = [
        str(test_dir / f"{target_base}.cpp"),
        str(test_dir / f"{target_base}_[a-z].cpp"),
    ]
    for pattern in patterns:
        for fpath in glob.glob(pattern):
            if exclude_path and Path(fpath).resolve() == exclude_path.resolve():
                continue
            text = Path(fpath).read_text(encoding="utf-8")
            for m in re.finditer(
                r"TEST(?:_[FP])?\(\w+,\s*(\w+)\)", text,
            ):
                existing_names.add(m.group(1))
    return existing_names


# ---------------------------------------------------------------------------
# Stage 4: Resolve filenames
# ---------------------------------------------------------------------------

def clause_to_filename(prefix, clause):
    """Convert prefix + clause to a target filename (without .cpp)."""
    if clause.startswith("non-lrm"):
        topic = clause.split(":", 1)[1] if ":" in clause else "misc"
        return f"test_non_lrm_{topic}"
    prefix = prefix.rstrip("_")
    if re.match(r"^[A-Z]$", clause):
        return f"{prefix}_annex_{clause.lower()}"
    annex_match = re.match(r"^([A-Z])\.(.+)$", clause)
    if annex_match:
        letter = annex_match.group(1).lower()
        parts = annex_match.group(2).split(".")
        padded = "_".join(p.zfill(2) for p in parts)
        return f"{prefix}_annex_{letter}_{padded}"
    parts = clause.split(".")
    padded = "_".join(p.zfill(2) for p in parts)
    return f"{prefix}_clause_{padded}"


def find_merge_target(target_base, test_dir, exclude_path=None):
    """Find an existing file to merge tests into."""
    exact = test_dir / f"{target_base}.cpp"
    if exact.exists():
        if not (exclude_path and exact.resolve() == exclude_path.resolve()):
            return exact
    variants = sorted(
        glob.glob(str(test_dir / f"{target_base}_[a-z].cpp")),
    )
    if exclude_path:
        resolved = exclude_path.resolve()
        variants = [v for v in variants
                    if Path(v).resolve() != resolved]
    if variants:
        return Path(variants[-1])
    return None


# ---------------------------------------------------------------------------
# Stage 5: Generate files
# ---------------------------------------------------------------------------

def load_lrm_titles(lrm_path):
    """Build clause -> title map from LRM."""
    titles = {}
    if not lrm_path.exists():
        return titles
    for line in lrm_path.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^(\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
    return titles


def generate_file(clause, title, parsed, tests):
    """Generate the content of a split test file."""
    out = []
    if clause == "non-lrm":
        out.append("// Non-LRM tests")
    elif re.match(r"^[A-Z]\.", clause):
        hdr = f"// Annex {clause}: {title}" if title else f"// Annex {clause}"
        out.append(hdr)
    else:
        hdr = f"// §{clause}: {title}" if title else f"// §{clause}"
        out.append(hdr)
    out.append("")
    for inc in parsed.includes:
        out.append(inc)
    out.append("")
    if parsed.using_line:
        out.append(parsed.using_line)
        out.append("")
    for item in parsed.global_preamble:
        for line in item.lines:
            cleaned = strip_lrm_quotes(line)
            if cleaned or cleaned == "":  # pragma: no branch
                out.append(cleaned)
        out.append("")
    for item in parsed.section_preamble:
        for line in item.lines:
            cleaned = strip_lrm_quotes(line)
            if cleaned or cleaned == "":  # pragma: no branch
                out.append(cleaned)
        out.append("")
    out.append("namespace {")
    out.append("")
    out.extend(_render_tests(tests))
    out.append("}  // namespace")
    out.append("")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Stage 6: Update CMakeLists.txt
# ---------------------------------------------------------------------------

def update_cmake(old_name, new_names, *, keep_old=False):
    """Update CMakeLists.txt: remove old entry, add new entries sorted."""
    text = CMAKE_PATH.read_text(encoding="utf-8")
    lines = text.splitlines()
    header_lines = []
    test_names = []
    for line in lines:
        m = re.match(r"add_unit_test\((\w+)\)", line.strip())
        if m:
            name = m.group(1)
            if name != old_name or keep_old:
                test_names.append(name)
        else:
            header_lines.append(line)
    test_names.extend(new_names)
    test_names = sorted(set(test_names))
    out_lines = header_lines
    for name in test_names:
        out_lines.append(f"add_unit_test({name})")
    CMAKE_PATH.write_text("\n".join(out_lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _parse_args():
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Split standalone test files into per-clause files.",
    )
    parser.add_argument(
        "--file", required=True, help="Path to the input test file",
    )
    parser.add_argument(
        "--output-dir", required=True, help="Directory for output files",
    )
    parser.add_argument(
        "--lrm", required=True,
        help="Path to IEEE 1800-2023 LRM text file",
    )
    parser.add_argument(
        "--arch", required=True,
        help="Path to ARCHITECTURE.md file",
    )
    parser.add_argument(
        "--max-lines", type=int, default=None,
        help="Maximum lines per output file; splits into _a, _b, ... suffixes",
    )
    parser.add_argument(
        "--test", required=True,
        help="Name of the single test to classify",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Classify only, don't write files",
    )
    return parser.parse_args()


def _format_clause(clause):
    """Format a clause for display."""
    if clause is None:
        return "(parse error)"
    if clause.startswith("non-lrm:"):
        tag = clause[len("non-lrm:"):].upper().replace("_", " ")
        return f"Non-LRM {tag}"
    return f"\u00a7{clause}"


def _wrap(label, value):
    """Wrap a labeled line to 80 chars with 2-space continuation indent."""
    return textwrap.fill(
        value, width=80,
        initial_indent=f"  {label}: ",
        subsequent_indent="  ",
    )


def _print_classification_table(tests):
    """Print the classification results as sub-reports."""
    for i, t in enumerate(tests):
        print(_wrap("Test", f"{t.test_name}()"))
        print(_wrap("Clause", _format_clause(t.clause)))
        print(_wrap("Rationale", t.rationale or ""))
        if i < len(tests) - 1:
            print("  ----")


def _group_tests(tests):
    """Group tests by (prefix, clause)."""
    groups = {}
    for t in tests:
        prefix = t.prefix or "test_non_lrm"
        clause = t.clause or "non-lrm"
        groups.setdefault((prefix, clause), []).append(t)
    return groups


def _report_removals(tests, existing, target, dry_run):
    """Print removal messages for duplicate tests and return count."""
    verb = "Would have removed" if dry_run else "Removed"
    count = 0
    for t in tests:
        if t.test_name in existing:
            count += 1
            print(f"  - {verb} {t.test_name}() because it"
                  f" belongs in {target}.cpp where it"
                  " already exists.")
    return count


def _resolve_destinations(
    groups, test_dir, exclude_path=None, dry_run=False,
):
    """Deduplicate tests and resolve create/merge destinations."""
    to_create = []
    to_merge = []
    n_removed = 0
    for (prefix, clause), tests in sorted(groups.items()):
        target = clause_to_filename(prefix, clause)
        existing = find_existing_tests(target, test_dir, exclude_path)
        unique = [t for t in tests if t.test_name not in existing]
        n_removed += _report_removals(tests, existing, target, dry_run)
        groups[(prefix, clause)] = unique
        if not unique:
            continue
        if exclude_path and exclude_path.stem == target:
            continue
        merge_path = find_merge_target(target, test_dir, exclude_path)
        if merge_path:
            to_merge.append((merge_path, unique))
        else:
            to_create.append((target, clause, unique))
    return to_create, to_merge, n_removed


def _write_creates(to_create, parsed, test_dir, lrm_titles, max_lines):
    """Write newly created clause files and return their names."""
    names = []
    for filename, clause, tests in to_create:
        title = lrm_titles.get(clause, "")
        batches = (_batch_tests(
            tests,
            len(generate_file(clause, title, parsed, []).splitlines()),
            max_lines,
        ) if max_lines else [tests])
        if len(batches) <= 1:
            content = generate_file(clause, title, parsed, tests)
            _write_one_file(filename, content, test_dir, names)
        else:
            for i, batch in enumerate(batches):
                suffix = chr(ord("a") + i)
                content = generate_file(clause, title, parsed, batch)
                _write_one_file(
                    f"{filename}_{suffix}", content, test_dir, names,
                )
    return names


def _write_files(to_create, to_merge, parsed, ctx):
    """Write new files and merge into existing files."""
    new_names = _write_creates(
        to_create, parsed, ctx["test_dir"],
        ctx["lrm_titles"], ctx.get("max_lines"),
    )
    for merge_path, tests in to_merge:
        split_names = append_tests_to_file(
            merge_path, parsed.global_preamble, tests,
            max_lines=ctx.get("max_lines"),
            section_preamble=parsed.section_preamble,
        )
        new_names.extend(split_names)
    return new_names


def _rewrite_source(filepath, groups, parsed, lrm_titles, test_name):
    """Rewrite the source file keeping only tests that belong there."""
    staying = [t for (p, c), ts in groups.items()
               if clause_to_filename(p, c) == test_name
               for t in ts]
    clause = next(c for (p, c), _ in groups.items()
                  if clause_to_filename(p, c) == test_name)
    title = lrm_titles.get(clause, "")
    content = generate_file(clause, title, parsed, staying)
    filepath.write_text(content, encoding="utf-8")
    return len(staying)


def _print_summary(
    to_create, to_merge, test_name, source_is_target, **kwargs,
):
    """Print the because-driven summary of what was done."""
    n_kept = kwargs.get("n_kept", 0)
    n_removed = kwargs.get("n_removed", 0)
    dry_run = kwargs.get("dry_run", False)

    def _v(past):
        """Return past future perfect tense if dry_run, else past."""
        if not dry_run:
            return past
        return f"Would have {past[0].lower()}{past[1:]}"

    print("\n  SUMMARY")
    if not to_create and not to_merge and source_is_target:
        if n_kept:
            print(f"  - {_v('Kept')} {n_kept} tests in"
                  f" {test_name}.cpp because they belong there.")
        if n_removed:
            rem = "to remove" if dry_run else "removed"
            print(f"  - {n_removed} duplicate(s) {rem}.")
        return
    for filename, _clause, tests in to_create:
        print(f"  - {_v('Created')} {filename}.cpp because"
              f" {len(tests)} test(s) belong there but the"
              " file did not exist.")
        print(f"  - {_v('Moved')} {len(tests)} test(s) to"
              f" {filename}.cpp because that's where they"
              " belong.")
    for merge_path, tests in to_merge:
        print(f"  - {_v('Moved')} {len(tests)} test(s) to"
              f" {merge_path.name} because that's where they"
              " belong.")
    if source_is_target and n_kept:
        print(f"  - {_v('Kept')} {n_kept} tests in"
              f" {test_name}.cpp because they belong there.")
    if not source_is_target:
        print(f"  - {_v('Deleted')} {test_name}.cpp because all"
              " its tests were moved elsewhere.")
        print(f"  - {_v('Updated')} CMakeLists.txt because"
              f" {test_name} was removed.")
    else:
        print(f"  - {_v('Updated')} CMakeLists.txt because"
              " new test targets were added.")


def _validate_input(filepath, test_name):
    """Parse and validate the input file, returning (parsed, target)."""
    if not filepath.exists():
        print(f"ERROR: {filepath} not found")
        sys.exit(1)
    parsed = parse_file(filepath)
    if not parsed.all_tests:
        print("ERROR: No TEST blocks found")
        sys.exit(1)
    matches = [t for t in parsed.all_tests if t.test_name == test_name]
    if not matches:
        print(f"ERROR: Test {test_name!r} not found in {filepath.name}")
        sys.exit(1)
    return parsed, matches[:1]


def _update_source(filepath, parsed, ctx):
    """Rewrite or remove the source file after moving a test."""
    others = [t for t in parsed.all_tests
              if t.test_name != ctx["test"]]
    source_is_target = ctx["source_is_target"]
    if source_is_target and others:
        content = generate_file("non-lrm", "", parsed, others)
        filepath.write_text(content, encoding="utf-8")
        return len(others)
    if source_is_target:
        return _rewrite_source(
            filepath, ctx["groups"], parsed,
            ctx["titles"], ctx["stem"],
        )
    if others:
        content = generate_file("non-lrm", "", parsed, others)
        filepath.write_text(content, encoding="utf-8")
    else:
        filepath.unlink()
    return 0


def _count_kept(groups, test_name):
    """Count tests that stay in the source file."""
    return sum(
        len(ts) for (p, c), ts in groups.items()
        if clause_to_filename(p, c) == test_name
    )


def _run(args):
    """Execute the split operation."""
    filepath = Path(args.file).resolve()
    test_name = filepath.stem
    parsed, target = _validate_input(filepath, args.test)
    print(f"{test_name}.cpp \u2014 {args.test}"
          f"{' (dry run)' if args.dry_run else ''}")
    classify_tests(
        target, parsed, Path(args.output_dir).resolve(),
        Path(args.lrm).resolve(), Path(args.arch).resolve(),
    )
    _print_classification_table(target)
    groups = _group_tests(target)
    source_is_target = any(
        clause_to_filename(p, c) == test_name
        for p, c in groups
    )
    to_create, to_merge, n_removed = _resolve_destinations(
        groups, Path(args.output_dir).resolve(),
        exclude_path=filepath, dry_run=args.dry_run,
    )
    n_kept = _count_kept(groups, test_name)
    if args.dry_run:
        _print_summary(to_create, to_merge, test_name,
                       source_is_target, n_kept=n_kept,
                       n_removed=n_removed, dry_run=True)
        return
    if not to_create and not to_merge and source_is_target \
            and n_removed == 0:
        _print_summary(to_create, to_merge, test_name,
                       source_is_target, n_kept=n_kept,
                       n_removed=n_removed)
        return
    titles = load_lrm_titles(Path(args.lrm).resolve())
    new_names = _write_files(to_create, to_merge, parsed, {
        "test_dir": Path(args.output_dir).resolve(),
        "lrm_titles": titles,
        "max_lines": getattr(args, "max_lines", None),
    })
    n_kept = _update_source(filepath, parsed, {
        "test": args.test, "groups": groups,
        "titles": titles, "stem": test_name,
        "source_is_target": source_is_target,
    })
    update_cmake(
        test_name, new_names,
        keep_old=source_is_target or any(
            t.test_name != args.test for t in parsed.all_tests
        ),
    )
    _print_summary(to_create, to_merge, test_name,
                   source_is_target, n_kept=n_kept,
                   n_removed=n_removed)


def main():
    """Entry point."""
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    _run(_parse_args())


if __name__ == "__main__":  # pragma: no cover
    main()
