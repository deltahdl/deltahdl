#!/usr/bin/env python3
"""Split standalone test files into per-LRM-clause files.

Usage:
  python3 scripts/split_tests.py --file path/to/test.cpp --output-dir path/to/out
  python3 scripts/split_tests.py --file path/to/test.cpp --output-dir path/to/out --dry-run
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


# ---------------------------------------------------------------------------
# Logging — tee stdout to ~/split_tests.log
# ---------------------------------------------------------------------------

class TeeWriter:
    """Write to multiple streams simultaneously."""

    def __init__(self, *streams):
        self.streams = streams

    def write(self, data):
        """Write data to all streams."""
        for s in self.streams:
            s.write(data)
            s.flush()

    def flush(self):
        """Flush all streams."""
        for s in self.streams:
            s.flush()


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
class SectionGroup:
    """A group of tests under a section header banner."""

    header_lines: list[str]
    preamble: list[PreambleItem]
    tests: list[TestBlock]


@dataclass
class ParsedFile:
    """Result of parsing a standalone test file."""

    includes: list[str]
    using_line: str | None
    has_namespace_wrapper: bool
    global_preamble: list[PreambleItem]
    sections: list[SectionGroup]
    all_tests: list[TestBlock]


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
LRM_PATH = Path.home() / "LRM.txt"
STANDALONE_PATH = Path.home() / "STANDALONE.md"
ARCH_PATH = REPO_ROOT / "docs" / "ARCHITECTURE.md"


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
        if stripped in ("}  // namespace", "} // namespace", ""):
            i += 1
            continue
        if stripped.startswith("//"):
            comments.append(lines[i].rstrip("\n"))
            i += 1
            continue
        if stripped == "namespace {":
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
    return g_pre, all_tests, has_ns


def parse_file(filepath):
    """Parse a standalone test file into structured components."""
    text = filepath.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)
    includes, using_line, hdr_ns, body_start = _parse_header(lines)
    g_pre, all_tests, body_ns = _parse_body(lines, body_start)
    return ParsedFile(
        includes=includes,
        using_line=using_line,
        has_namespace_wrapper=hdr_ns or body_ns,
        global_preamble=g_pre,
        sections=[],
        all_tests=all_tests,
    )


# ---------------------------------------------------------------------------
# Stage 2: Classify via Claude
# ---------------------------------------------------------------------------

def load_lrm_toc():
    """Load LRM table of contents (first ~2500 lines)."""
    if not LRM_PATH.exists():
        return "(LRM not found)"
    lines = LRM_PATH.read_text(encoding="utf-8").splitlines()
    return "\n".join(lines[:2500])


def load_architecture():
    """Load architecture doc."""
    if not ARCH_PATH.exists():
        return "(ARCHITECTURE.md not found)"
    return ARCH_PATH.read_text(encoding="utf-8")


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


def _build_test_blocks_text(tests):
    """Build text representation of test blocks for the prompt."""
    parts = []
    for t in tests:
        parts.append(
            f"\n--- TEST({t.suite_name}, {t.test_name}) ---\n",
        )
        parts.extend(line + "\n" for line in t.preceding_comments)
        parts.extend(line + "\n" for line in t.lines)
    return "".join(parts)


_PROMPT_TEMPLATE = """Classify each TEST block below. For each test determine:

1. PREFIX — which architectural pipeline stage the test exercises.
   You MUST use one of these exact prefixes:
   - test_preprocessor_ (preprocessor: macro expansion, `include, `ifdef)
   - test_lexer_ (lexer/tokenizer)
   - test_parser_ (parser and AST construction)
   - test_elaborator_ (elaborator: type checking, constant evaluation,
     sensitivity analysis, RTLIR)
   - test_simulator_ (simulator: scheduler, processes, eval, VCD, VPI, DPI,
     clocking, assertions, compiled sim, coverage, CRV, SDF)
   - test_synthesizer_ (synthesizer: AIG, optimization, LUT/cell mapping,
     netlist output)
   - test_non_lrm_ (internal infrastructure with no LRM clause)
   Do NOT invent new prefixes. Every test fits one of these categories.

2. CLAUSE — which IEEE 1800-2023 clause the test covers based on what the
   code actually DOES. Ignore source comments — they may be wrong.
   Use the most specific subclause possible (W.X.Y.Z).
   For annexes use: I.3, A.6, K.2, M.1, etc.
   If no LRM clause applies use: non-lrm

3. NON_LRM_TOPIC — if and only if the clause is "non-lrm", provide a short
   snake_case topic describing what the test exercises (e.g., "aig",
   "type_eval", "arena", "dpi_helpers"). This becomes the filename suffix:
   test_non_lrm_{{topic}}.cpp. If clause is NOT "non-lrm", set to null.{topics}

Project Architecture:
{arch}

LRM Table of Contents:
{toc}

TEST blocks:
{blocks}

IMPORTANT: Respond with ONLY a JSON object matching this schema:
{{"tests": [
  {{"test_name": "...", "prefix": "...", "clause": "...",
    "non_lrm_topic": "...", "rationale": "..."}}
]}}
"""


def _build_prompt(tests, test_dir):
    """Build the Claude classification prompt."""
    topics = existing_non_lrm_topics(test_dir)
    topics_hint = ""
    if topics:
        topics_hint = (
            "\n   Existing non-lrm topic files: "
            + ", ".join(topics)
            + "\n   PREFER reusing one of these topics when the"
            " test fits, to avoid near-duplicate filenames."
        )
    return _PROMPT_TEMPLATE.format(
        topics=topics_hint,
        arch=load_architecture(),
        toc=load_lrm_toc(),
        blocks=_build_test_blocks_text(tests),
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
        ["claude", "-p", "--model", "sonnet"],
        input=prompt,
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    print(f"  Claude RC={result.returncode}")
    if result.stderr.strip():
        print(f"  Claude stderr: {result.stderr[:300]}")
    if result.returncode != 0:
        print(f"ERROR: Claude CLI failed:\n{result.stderr}")
        sys.exit(1)
    return _extract_json(result.stdout.strip())


def _build_result_map(response):
    """Build lookup map from classification response."""
    result_map = {}
    for item in response.get("tests", []):
        name = item["test_name"]
        tm = re.match(r"TEST(?:_[FP])?\((.+)\)$", name)
        if tm:
            name = tm.group(1)
            item["test_name"] = name
        result_map[name] = item
        for sep in ("_", ".", "/", ", ", "::"):
            if sep in name:
                result_map[name.split(sep, 1)[-1]] = item
    return result_map


def _apply_classifications(tests, result_map):
    """Apply classification results to test blocks."""
    for t in tests:
        if t.test_name not in result_map:
            print(
                f"  WARNING: Claude did not classify "
                f"{t.test_name}, defaulting to non-lrm",
            )
            t.prefix = "test_non_lrm"
            t.clause = "non-lrm"
            continue
        r = result_map[t.test_name]
        t.prefix = r["prefix"]
        clause = r["clause"]
        if clause.replace("_", "-") == "non-lrm":
            clause = "non-lrm"
        topic = r.get("non_lrm_topic")
        if clause == "non-lrm" and topic:
            clause = f"non-lrm:{topic}"
        t.clause = clause
        t.rationale = r.get("rationale", "")


def classify_tests(tests, test_dir):
    """Use Claude to classify each test's prefix and clause."""
    prompt = _build_prompt(tests, test_dir)
    print("  Calling Claude for classification...")
    response = _call_claude(prompt)
    count = len(response.get("tests", []))
    print(f"  Parsed {count} test classifications")
    result_map = _build_result_map(response)
    expected = {t.test_name for t in tests}
    returned = {
        item["test_name"] for item in response.get("tests", [])
    }
    if expected != returned:
        missing = expected - set(result_map.keys())
        if missing:
            print(f"  Name mismatch — returned: "
                  f"{sorted(returned)[:5]}...")
            print(f"  Expected: {sorted(expected)[:5]}...")
    _apply_classifications(tests, result_map)
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

def load_lrm_titles():
    """Build clause -> title map from LRM."""
    titles = {}
    if not LRM_PATH.exists():
        return titles
    for line in LRM_PATH.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^(\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
    return titles


def strip_lrm_quotes(line):
    """Remove LRM prose quotes from comments."""
    if re.search(r'//.*"[A-Z].*"', line):
        m = re.match(r'(//\s*§[\d.]+:?\s*)(".*")', line)
        if m:
            return m.group(1).rstrip()
        return ""
    return line


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
    out.append("namespace {")
    out.append("")
    for t in tests:
        for line in t.preceding_comments:
            cleaned = strip_lrm_quotes(line)
            if cleaned:
                out.append(cleaned)
        for line in t.lines:
            out.append(strip_lrm_quotes(line))
        out.append("")
    out.append("}  // namespace")
    out.append("")
    return "\n".join(out)


def append_tests_to_file(filepath, global_preamble, tests):
    """Append tests to an existing file before closing }  // namespace."""
    text = filepath.read_text(encoding="utf-8")
    lines = text.splitlines()
    insert_idx = len(lines)
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() in ("}  // namespace", "} // namespace"):
            insert_idx = i
            break
    new_lines = []
    for item in global_preamble:
        first_code = next(
            (ln for ln in item.lines if not ln.strip().startswith("//")),
            item.lines[0],
        )
        if first_code.strip() not in text:
            new_lines.extend(item.lines)
            new_lines.append("")
    for t in tests:
        for line in t.preceding_comments:
            cleaned = strip_lrm_quotes(line)
            if cleaned:
                new_lines.append(cleaned)
        for line in t.lines:
            new_lines.append(strip_lrm_quotes(line))
        new_lines.append("")
    lines[insert_idx:insert_idx] = new_lines
    filepath.write_text("\n".join(lines) + "\n", encoding="utf-8")


# ---------------------------------------------------------------------------
# Stage 6: Update CMakeLists.txt
# ---------------------------------------------------------------------------

def update_cmake(old_name, new_names):
    """Update CMakeLists.txt: remove old entry, add new entries sorted."""
    text = CMAKE_PATH.read_text(encoding="utf-8")
    lines = text.splitlines()
    header_lines = []
    test_names = []
    for line in lines:
        m = re.match(r"add_unit_test\((\w+)\)", line.strip())
        if m:
            name = m.group(1)
            if name != old_name:
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
# Stage 7: Clean up and commit
# ---------------------------------------------------------------------------

def update_standalone(test_name):
    """Remove entry from ~/STANDALONE.md."""
    if not STANDALONE_PATH.exists():
        return
    text = STANDALONE_PATH.read_text(encoding="utf-8")
    lines = text.splitlines()
    out = [ln for ln in lines if f"- [ ] {test_name}" not in ln]
    STANDALONE_PATH.write_text(
        "\n".join(out) + "\n", encoding="utf-8",
    )


def commit_and_push(test_name, n_files):
    """Git add, commit, push."""
    co = "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    subprocess.run(
        ["git", "add", "-A"], cwd=REPO_ROOT, check=True,
    )
    if n_files == 0:
        msg = f"Remove {test_name} (all tests are duplicates)"
    else:
        msg = f"Split {test_name} into {n_files} per-clause files"
    subprocess.run(
        ["git", "commit", "-m", f"{msg}\n\n{co}"],
        cwd=REPO_ROOT,
        check=True,
    )
    r = subprocess.run(
        ["git", "push"], cwd=REPO_ROOT, check=False,
    )
    if r.returncode != 0:
        print(f"  WARNING: git push failed (rc={r.returncode})")


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
        "--dry-run", action="store_true",
        help="Classify only, don't write files",
    )
    return parser.parse_args()


def _print_classification_table(tests):
    """Print the classification results table."""
    print("\n  Classification results:")
    print(f"  {'Test':<45} {'Prefix':<15} "
          f"{'Clause':<12} Rationale")
    print(f"  {'-'*45} {'-'*15} {'-'*12} {'-'*40}")
    for t in tests:
        print(f"  {t.test_name:<45} {t.prefix:<15} "
              f"{t.clause:<12} {t.rationale}")
    print()


def _group_tests(tests):
    """Group tests by (prefix, clause)."""
    groups = {}
    for t in tests:
        prefix = t.prefix or "test_non_lrm"
        clause = t.clause or "non-lrm"
        groups.setdefault((prefix, clause), []).append(t)
    return groups


def _resolve_destinations(groups, test_dir, lrm_titles,
                          exclude_path=None):
    """Deduplicate tests and resolve create/merge destinations."""
    to_create = []
    to_merge = []
    for (prefix, clause), tests in sorted(groups.items()):
        target = clause_to_filename(prefix, clause)
        existing = find_existing_tests(target, test_dir, exclude_path)
        unique = [t for t in tests if t.test_name not in existing]
        for d in tests:
            if d.test_name in existing:
                print(f"  DUPLICATE: {d.test_name} already in "
                      f"{target} — dropping")
        if not unique:
            print(f"  All tests for {clause} are duplicates")
            continue
        merge_path = find_merge_target(target, test_dir, exclude_path)
        if merge_path:
            to_merge.append((merge_path, unique))
            print(f"  Merging {len(unique)} tests into "
                  f"{merge_path.name}")
        else:
            title = lrm_titles.get(clause, "")
            to_create.append((target, clause, unique))
            print(f"  {target}.cpp: {len(unique)} tests "
                  f"(§{clause}: {title})")
    return to_create, to_merge


def _write_files(to_create, to_merge, parsed, test_dir, lrm_titles):
    """Write new files and merge into existing files."""
    new_names = []
    for filename, clause, tests in to_create:
        title = lrm_titles.get(clause, "")
        content = generate_file(clause, title, parsed, tests)
        outpath = test_dir / f"{filename}.cpp"
        outpath.write_text(content, encoding="utf-8")
        new_names.append(filename)
        print(f"  Created {filename}.cpp ({len(tests)} tests)")
    for merge_path, tests in to_merge:
        append_tests_to_file(
            merge_path, parsed.global_preamble, tests,
        )
        print(f"  Merged {len(tests)} tests into {merge_path.name}")
    return new_names


def _run(args):
    """Execute the split operation."""
    test_dir = Path(args.output_dir).resolve()
    filepath = Path(args.file).resolve()
    test_name = filepath.stem
    if not filepath.exists():
        print(f"ERROR: {filepath} not found")
        sys.exit(1)
    mode = "DRY RUN" if args.dry_run else "LIVE"
    print(f"=== Splitting {test_name} ({mode}) ===")
    print("Stage 1: Parsing...")
    parsed = parse_file(filepath)
    print(f"  Found {len(parsed.all_tests)} tests, "
          f"{len(parsed.global_preamble)} preamble items")
    if not parsed.all_tests:
        print("ERROR: No TEST blocks found")
        sys.exit(1)
    print("Stage 2: Classifying via Claude...")
    classify_tests(parsed.all_tests, test_dir)
    _print_classification_table(parsed.all_tests)
    print("Stage 3: Checking for duplicates...")
    groups = _group_tests(parsed.all_tests)
    lrm_titles = load_lrm_titles()
    to_create, to_merge = _resolve_destinations(
        groups, test_dir, lrm_titles, exclude_path=filepath,
    )
    if args.dry_run:
        print(f"\n=== DRY RUN complete. Would create "
              f"{len(to_create)}, merge into "
              f"{len(to_merge)} files. ===")
        return
    n_created = len(to_create)
    n_merged = len(to_merge)
    print(f"\nStage 5: Creating {n_created}, "
          f"merging into {n_merged} files...")
    new_names = _write_files(
        to_create, to_merge, parsed, test_dir, lrm_titles,
    )
    print("Stage 6: Updating CMakeLists.txt...")
    update_cmake(test_name, new_names)
    print("Stage 7: Cleaning up...")
    if test_name not in new_names:
        filepath.unlink()
        print(f"  Deleted {test_name}.cpp")
    update_standalone(test_name)
    print("  Removed from STANDALONE.md")
    n_total = n_created + n_merged
    print("Stage 7: Committing and pushing...")
    commit_and_push(test_name, n_total)
    print(f"\nDone! Created {n_created}, merged into {n_merged} files.")


def main():
    """Entry point — sets up logging then runs."""
    log_path = Path.home() / "split_tests.log"
    with log_path.open("a", encoding="utf-8") as log:
        sys.stdout = TeeWriter(sys.__stdout__, log)
        sys.stderr = TeeWriter(sys.__stderr__, log)
        _run(_parse_args())


if __name__ == "__main__":  # pragma: no cover
    main()
