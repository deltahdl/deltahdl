#!/usr/bin/env python3
"""Split standalone test files into per-LRM-clause files.

Usage:
  python3 ~/split_tests.py --file /path/to/test_foo.cpp --output-dir /path/to/out
  python3 ~/split_tests.py --file /path/to/test_foo.cpp --output-dir /path/to/out --dry-run
"""

import argparse
import glob
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Logging — tee stdout to ~/split_tests.log
# ---------------------------------------------------------------------------

class TeeWriter:
    def __init__(self, *streams):
        self.streams = streams
    def write(self, data):
        for s in self.streams:
            s.write(data)
            s.flush()
    def flush(self):
        for s in self.streams:
            s.flush()

LOG_FILE = open(Path.home() / "split_tests.log", "a")
sys.stdout = TeeWriter(sys.__stdout__, LOG_FILE)
sys.stderr = TeeWriter(sys.__stderr__, LOG_FILE)


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class TestBlock:
    suite_name: str
    test_name: str
    lines: list[str]
    preceding_comments: list[str]
    prefix: str | None = None
    clause: str | None = None
    non_lrm_topic: str | None = None
    rationale: str | None = None


@dataclass
class PreambleItem:
    lines: list[str]


@dataclass
class SectionGroup:
    header_lines: list[str]
    preamble: list[PreambleItem]
    tests: list[TestBlock]


@dataclass
class ParsedFile:
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
            print("ERROR: Cannot find repo root (looking for test/CMakeLists.txt)")
            sys.exit(1)
        d = parent

REPO_ROOT = find_repo_root()

TEST_DIR = None  # Set by --output-dir
CMAKE_PATH = REPO_ROOT / "test" / "CMakeLists.txt"
LRM_PATH = Path.home() / "LRM.txt"
STANDALONE_PATH = Path.home() / "STANDALONE.md"
ARCH_PATH = REPO_ROOT / "docs" / "ARCHITECTURE.md"


# ---------------------------------------------------------------------------
# Stage 1: Parse
# ---------------------------------------------------------------------------

def extract_brace_block(lines: list[str], start_idx: int) -> tuple[list[str], int]:
    """Extract a brace-delimited block starting from start_idx."""
    depth = 0
    block: list[str] = []
    in_string = False
    in_block_comment = False

    for i in range(start_idx, len(lines)):
        line = lines[i]
        block.append(line)

        j = 0
        while j < len(line):
            ch = line[j]
            if in_block_comment:
                if ch == "*" and j + 1 < len(line) and line[j + 1] == "/":
                    in_block_comment = False
                    j += 1
            elif in_string:
                if ch == "\\":
                    j += 1  # skip escaped char
                elif ch == '"':
                    in_string = False
            elif ch == "/" and j + 1 < len(line) and line[j + 1] == "/":
                break  # rest of line is comment
            elif ch == "/" and j + 1 < len(line) and line[j + 1] == "*":
                in_block_comment = True
                j += 1
            elif ch == '"':
                in_string = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    return block, i
            j += 1

    raise ValueError(f"Unmatched brace starting at line {start_idx + 1}")


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


def is_preamble_start(line: str) -> bool:
    """Check if a line starts a preamble item (struct, static func, enum, etc.)."""
    stripped = line.strip()
    if stripped.startswith("struct ") or stripped.startswith("class "):
        return True
    if stripped.startswith("static ") and "(" in stripped:
        return True
    if stripped.startswith("enum ") or stripped.startswith("enum class "):
        return True
    if stripped.startswith("typedef "):
        return True
    # Non-static functions (may be in anonymous namespace)
    if re.match(r"^(void|bool|int|uint\w+|auto|const\s|static\s|inline\s)", stripped):
        if "(" in stripped and not stripped.startswith("//"):
            return True
    return False


def parse_file(filepath: Path) -> ParsedFile:
    """Parse a standalone test file into structured components."""
    text = filepath.read_text()
    lines = text.splitlines(keepends=True)

    includes: list[str] = []
    using_line: str | None = None
    has_namespace_wrapper = False
    global_preamble: list[PreambleItem] = []
    all_tests: list[TestBlock] = []

    i = 0
    # Skip file header comments
    while i < len(lines) and not lines[i].strip().startswith("#include"):
        i += 1

    # Extract includes
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("#include"):
            includes.append(lines[i].rstrip("\n"))
            i += 1
        elif stripped == "":
            i += 1
        else:
            break

    # Check for using namespace
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("using namespace"):
            using_line = lines[i].rstrip("\n")
            i += 1
            break
        elif stripped == "":
            i += 1
        else:
            break

    # Skip blank lines
    while i < len(lines) and lines[i].strip() == "":
        i += 1

    # Check for namespace {
    if i < len(lines) and lines[i].strip() == "namespace {":
        has_namespace_wrapper = True
        i += 1

    # Now parse the body: preamble items, section headers, TEST blocks
    current_comments: list[str] = []
    in_global = True  # True until we hit first section header or TEST
    current_section_preamble: list[PreambleItem] = []
    sections: list[SectionGroup] = []
    current_section_header: list[str] = []

    while i < len(lines):
        stripped = lines[i].strip()

        # Skip closing namespace
        if stripped == "}  // namespace" or stripped == "} // namespace":
            i += 1
            continue

        # Blank line
        if stripped == "":
            i += 1
            continue

        # Comment line
        if stripped.startswith("//"):
            current_comments.append(lines[i].rstrip("\n"))

            # Check if this is a section header banner
            if is_section_header(lines[i]):
                # Look ahead: is next non-blank line also a comment (title line)?
                # Section headers are usually: === banner, title, === banner
                pass

            i += 1
            continue

        # Skip namespace { (may appear later in file, not just at start)
        if stripped == "namespace {":
            has_namespace_wrapper = True
            i += 1
            continue

        # TEST block (TEST, TEST_F, TEST_P)
        m = re.match(r"^TEST(?:_[FP])?\((\w+),\s*(\w+)\)", stripped)
        if m:
            in_global = False
            test_lines, end_idx = extract_brace_block(lines, i)
            tb = TestBlock(
                suite_name=m.group(1),
                test_name=m.group(2),
                lines=[l.rstrip("\n") for l in test_lines],
                preceding_comments=current_comments[:],
            )
            all_tests.append(tb)
            current_comments.clear()
            i = end_idx + 1
            continue

        # Preamble item (struct, function, enum, etc.)
        if "{" in stripped:
            try:
                block_lines, end_idx = extract_brace_block(lines, i)
                item = PreambleItem(lines=[l.rstrip("\n") for l in block_lines])
                # Include preceding comments as part of the item
                if current_comments:
                    item.lines = current_comments + item.lines
                    current_comments.clear()
                if in_global:
                    global_preamble.append(item)
                else:
                    current_section_preamble.append(item)
                i = end_idx + 1
                continue
            except ValueError:
                pass

        # Single-line declarations (constexpr, static const, etc.)
        if stripped.endswith(";"):
            decl_lines = current_comments + [lines[i].rstrip("\n")]
            current_comments.clear()
            item = PreambleItem(lines=decl_lines)
            if in_global:
                global_preamble.append(item)
            else:
                current_section_preamble.append(item)
            i += 1
            continue

        # Anything else — treat as a comment/misc line
        current_comments.append(lines[i].rstrip("\n"))
        i += 1

    return ParsedFile(
        includes=includes,
        using_line=using_line,
        has_namespace_wrapper=has_namespace_wrapper,
        global_preamble=global_preamble,
        sections=sections,
        all_tests=all_tests,
    )


# ---------------------------------------------------------------------------
# Stage 2: Classify via Claude
# ---------------------------------------------------------------------------

def load_lrm_toc() -> str:
    """Load LRM table of contents (first ~2500 lines)."""
    if not LRM_PATH.exists():
        return "(LRM not found)"
    lines = LRM_PATH.read_text().splitlines()
    # ToC is in the first ~2500 lines
    return "\n".join(lines[:2500])


def load_architecture() -> str:
    """Load architecture doc."""
    if not ARCH_PATH.exists():
        return "(ARCHITECTURE.md not found)"
    return ARCH_PATH.read_text()


def existing_non_lrm_topics() -> list[str]:
    """Scan output dir for existing test_non_lrm_*.cpp files and extract topic names."""
    topics: set[str] = set()
    for fpath in sorted(glob.glob(str(TEST_DIR / "test_non_lrm_*.cpp"))):
        stem = Path(fpath).stem  # e.g. "test_non_lrm_aig"
        topic = stem[len("test_non_lrm_"):]
        # Strip multi-part suffix (_a, _b, etc.)
        if topic and topic[-1].isalpha() and len(topic) >= 2 and topic[-2] == "_":
            topic = topic[:-2]
        if topic:
            topics.add(topic)
    return sorted(topics)


def classify_tests(tests: list[TestBlock]) -> list[TestBlock]:
    """Use Claude to classify each test's prefix and clause."""
    lrm_toc = load_lrm_toc()
    architecture = load_architecture()

    test_blocks_text = ""
    for t in tests:
        test_blocks_text += f"\n--- TEST({t.suite_name}, {t.test_name}) ---\n"
        for line in t.preceding_comments:
            test_blocks_text += line + "\n"
        for line in t.lines:
            test_blocks_text += line + "\n"

    existing_topics = existing_non_lrm_topics()
    if existing_topics:
        topics_hint = (
            "\n   Existing non-lrm topic files: " + ", ".join(existing_topics) +
            "\n   PREFER reusing one of these topics when the test fits, to avoid"
            " near-duplicate filenames."
        )
    else:
        topics_hint = ""

    prompt = f"""Classify each TEST block below. For each test determine:

1. PREFIX — which architectural pipeline stage the test exercises.
   You MUST use one of these exact prefixes:
   - test_preprocessor_ (preprocessor: macro expansion, `include, `ifdef)
   - test_lexer_ (lexer/tokenizer)
   - test_parser_ (parser and AST construction)
   - test_elaborator_ (elaborator: type checking, constant evaluation, sensitivity analysis, RTLIR)
   - test_simulator_ (simulator: scheduler, processes, eval, VCD, VPI, DPI, clocking, assertions, compiled sim, coverage, CRV, SDF)
   - test_synthesizer_ (synthesizer: AIG, optimization, LUT/cell mapping, netlist output)
   - test_non_lrm_ (internal infrastructure with no LRM clause)
   Do NOT invent new prefixes. Every test fits one of these categories.

2. CLAUSE — which IEEE 1800-2023 clause the test covers based on what the
   code actually DOES. Ignore source comments — they may be wrong.
   Use the most specific subclause possible (W.X.Y.Z).
   For annexes use: I.3, A.6, K.2, M.1, etc.
   If no LRM clause applies use: non-lrm

3. NON_LRM_TOPIC — if and only if the clause is "non-lrm", provide a short
   snake_case topic describing what the test exercises (e.g., "aig", "type_eval",
   "arena", "dpi_helpers"). This becomes the filename suffix:
   test_non_lrm_{{topic}}.cpp. If the clause is NOT "non-lrm", set this to null.{topics_hint}

Project Architecture:
{architecture}

LRM Table of Contents:
{lrm_toc}

TEST blocks:
{test_blocks_text}

IMPORTANT: Respond with ONLY a JSON object matching this exact schema — no markdown, no explanation, no text before or after the JSON:
{{"tests": [{{"test_name": "...", "prefix": "...", "clause": "...", "non_lrm_topic": "...", "rationale": "..."}}]}}
"""

    print("  Calling Claude for classification...")
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    result = subprocess.run(
        [
            "claude", "-p",
            "--model", "sonnet",
        ],
        input=prompt,
        capture_output=True,
        text=True,
        env=env,
    )

    print(f"  Claude RC={result.returncode}")
    if result.stderr.strip():
        print(f"  Claude stderr: {result.stderr[:300]}")

    if result.returncode != 0:
        print(f"ERROR: Claude CLI failed:\n{result.stderr}")
        sys.exit(1)

    # Parse JSON from the plain text response.
    # The model should return a JSON object, possibly with surrounding text.
    text = result.stdout.strip()
    try:
        response = json.loads(text)
    except json.JSONDecodeError:
        # Extract JSON object from surrounding text
        start = text.find("{")
        end = text.rfind("}") + 1
        if start >= 0 and end > start:
            try:
                response = json.loads(text[start:end])
            except json.JSONDecodeError:
                print(f"ERROR: Could not extract JSON from response:\n{text[:1000]}")
                sys.exit(1)
        else:
            print(f"ERROR: No JSON object found in response:\n{text[:1000]}")
            sys.exit(1)

    print(f"  Parsed {len(response.get('tests', []))} test classifications")

    # Map results back to test blocks.
    # Claude may return test_name as "SuiteName_TestName", "SuiteName.TestName",
    # or just "TestName". Build maps for all variants.
    result_map = {}
    for item in response.get("tests", []):
        name = item["test_name"]
        # Strip TEST(...) wrapper if present: "TEST(Suite, Name)" -> "Suite, Name"
        tm = re.match(r"TEST(?:_[FP])?\((.+)\)$", name)
        if tm:
            name = tm.group(1)
            item["test_name"] = name
        result_map[name] = item
        # Also store with suite prefix stripped via various separators
        for sep in ["_", ".", "/", ", ", "::"]:
            if sep in name:
                result_map[name.split(sep, 1)[-1]] = item

    expected = {t.test_name for t in tests}
    returned = {item["test_name"] for item in response.get("tests", [])}
    if expected != returned:
        missing = expected - set(result_map.keys())
        if missing:
            print(f"  Name mismatch debug — returned names: {sorted(returned)[:5]}...")
            print(f"  Expected names: {sorted(expected)[:5]}...")

    for t in tests:
        if t.test_name in result_map:
            r = result_map[t.test_name]
            t.prefix = r["prefix"]
            # Normalize: LLM sometimes returns "non_lrm" instead of "non-lrm"
            clause = r["clause"]
            if clause.replace("_", "-") == "non-lrm":
                clause = "non-lrm"
            t.clause = clause
            t.non_lrm_topic = r.get("non_lrm_topic")
            t.rationale = r.get("rationale", "")
        else:
            print(f"  WARNING: Claude did not classify {t.test_name}, defaulting to non-lrm")
            t.prefix = "test_non_lrm"
            t.clause = "non-lrm"

    return tests


# ---------------------------------------------------------------------------
# Stage 3: Deduplicate
# ---------------------------------------------------------------------------

def find_existing_tests(target_base: str) -> set[str]:
    """Find TEST names in existing clause files matching target_base."""
    existing_names: set[str] = set()
    # Check exact match and multi-part variants
    patterns = [
        str(TEST_DIR / f"{target_base}.cpp"),
        str(TEST_DIR / f"{target_base}_[a-z].cpp"),
    ]
    for pattern in patterns:
        for fpath in glob.glob(pattern):
            text = Path(fpath).read_text()
            for m in re.finditer(r"TEST(?:_[FP])?\(\w+,\s*(\w+)\)", text):
                existing_names.add(m.group(1))
    return existing_names


# ---------------------------------------------------------------------------
# Stage 4: Resolve filenames
# ---------------------------------------------------------------------------

def clause_to_filename(prefix: str, clause: str, original_name: str) -> str:
    """Convert prefix + clause to a target filename (without .cpp)."""
    if clause.startswith("non-lrm"):
        if ":" in clause:
            topic = clause.split(":", 1)[1]
        else:
            topic = "misc"
        return f"test_non_lrm_{topic}"

    # Strip trailing _ from prefix if present
    prefix = prefix.rstrip("_")

    # Annex: A.6.3 -> test_sim_annex_a_06_03
    annex_match = re.match(r"^([A-Z])\.(.+)$", clause)
    if annex_match:
        letter = annex_match.group(1).lower()
        parts = annex_match.group(2).split(".")
        padded = "_".join(p.zfill(2) for p in parts)
        return f"{prefix}_annex_{letter}_{padded}"

    # Clause: 4.9.5 -> test_sim_clause_04_09_05
    parts = clause.split(".")
    padded = "_".join(p.zfill(2) for p in parts)
    return f"{prefix}_clause_{padded}"


def find_merge_target(target_base: str) -> Path | None:
    """Find an existing file to merge tests into."""
    exact = TEST_DIR / f"{target_base}.cpp"
    if exact.exists():
        return exact
    variants = sorted(glob.glob(str(TEST_DIR / f"{target_base}_[a-z].cpp")))
    if variants:
        return Path(variants[-1])
    return None


# ---------------------------------------------------------------------------
# Stage 5: Generate files
# ---------------------------------------------------------------------------

def load_lrm_titles() -> dict[str, str]:
    """Build clause -> title map from LRM."""
    titles: dict[str, str] = {}
    if not LRM_PATH.exists():
        return titles
    for line in LRM_PATH.read_text().splitlines():
        # Match: 4.9.5 Switch (transistor) processing
        m = re.match(r"^(\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
        # Match: I.3 Source code
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
    return titles


def strip_lrm_quotes(line: str) -> str:
    """Remove LRM prose quotes from comments."""
    # Match: // §X.Y.Z: "quoted text..."  or  // "quoted text..."
    if re.search(r'//.*"[A-Z].*"', line):
        # Keep just the section reference, drop the quote
        m = re.match(r'(//\s*§[\d.]+:?\s*)(".*")', line)
        if m:
            return m.group(1).rstrip()
        # If it's just a bare quote, remove the line entirely
        return ""
    return line


def generate_file(
    clause: str,
    title: str,
    includes: list[str],
    using_line: str | None,
    global_preamble: list[PreambleItem],
    tests: list[TestBlock],
) -> str:
    """Generate the content of a split test file."""
    out: list[str] = []

    # Section comment
    if clause == "non-lrm":
        out.append(f"// Non-LRM tests")
    elif re.match(r"^[A-Z]\.", clause):
        out.append(f"// Annex {clause}: {title}" if title else f"// Annex {clause}")
    else:
        out.append(f"// §{clause}: {title}" if title else f"// §{clause}")

    out.append("")

    # Includes
    for inc in includes:
        out.append(inc)

    out.append("")

    # Using namespace
    if using_line:
        out.append(using_line)
        out.append("")

    # Global preamble
    for item in global_preamble:
        for line in item.lines:
            cleaned = strip_lrm_quotes(line)
            if cleaned or cleaned == "":
                out.append(cleaned)
        out.append("")

    # Namespace wrapper
    out.append("namespace {")
    out.append("")

    # Tests
    for t in tests:
        for line in t.preceding_comments:
            cleaned = strip_lrm_quotes(line)
            if cleaned:
                out.append(cleaned)
        for line in t.lines:
            cleaned = strip_lrm_quotes(line)
            out.append(cleaned)
        out.append("")

    out.append("}  // namespace")
    out.append("")

    return "\n".join(out)


def append_tests_to_file(filepath: Path, global_preamble: list[PreambleItem],
                         tests: list[TestBlock]):
    """Append tests to an existing file before closing }  // namespace."""
    text = filepath.read_text()
    lines = text.splitlines()

    # Find }  // namespace
    insert_idx = len(lines)
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip() in ("}  // namespace", "} // namespace"):
            insert_idx = i
            break

    new_lines: list[str] = []

    # Add preamble items not already in the file
    for item in global_preamble:
        first_code = next((l for l in item.lines if not l.strip().startswith("//")),
                          item.lines[0])
        if first_code.strip() not in text:
            for line in item.lines:
                new_lines.append(line)
            new_lines.append("")

    # Add tests
    for t in tests:
        for line in t.preceding_comments:
            cleaned = strip_lrm_quotes(line)
            if cleaned:
                new_lines.append(cleaned)
        for line in t.lines:
            cleaned = strip_lrm_quotes(line)
            new_lines.append(cleaned)
        new_lines.append("")

    lines[insert_idx:insert_idx] = new_lines
    filepath.write_text("\n".join(lines) + "\n")


# ---------------------------------------------------------------------------
# Stage 6: Update CMakeLists.txt
# ---------------------------------------------------------------------------

def update_cmake(old_name: str, new_names: list[str]):
    """Update CMakeLists.txt: remove old entry, add new entries in sorted order."""
    text = CMAKE_PATH.read_text()
    lines = text.splitlines()
    header_lines: list[str] = []
    test_names: list[str] = []

    for line in lines:
        m = re.match(r"add_unit_test\((\w+)\)", line.strip())
        if m:
            name = m.group(1)
            if name == old_name:
                continue  # Remove old entry
            test_names.append(name)
        else:
            header_lines.append(line)

    # Add new entries and sort
    test_names.extend(new_names)
    test_names = sorted(set(test_names))

    out_lines = header_lines
    for name in test_names:
        out_lines.append(f"add_unit_test({name})")

    CMAKE_PATH.write_text("\n".join(out_lines) + "\n")


# ---------------------------------------------------------------------------
# Stage 7: Clean up and commit
# ---------------------------------------------------------------------------

def update_standalone(test_name: str):
    """Remove entry from ~/STANDALONE.md."""
    if not STANDALONE_PATH.exists():
        return
    text = STANDALONE_PATH.read_text()
    lines = text.splitlines()
    out = [l for l in lines if f"- [ ] {test_name}" not in l]
    STANDALONE_PATH.write_text("\n".join(out) + "\n")


def commit_and_push(test_name: str, n_files: int):
    """Git add, commit, push."""
    subprocess.run(["git", "add", "-A"], cwd=REPO_ROOT, check=True)
    if n_files == 0:
        msg = f"Remove {test_name} (all tests are duplicates)\n\nCo-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    else:
        msg = f"Split {test_name} into {n_files} per-clause files\n\nCo-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    subprocess.run(
        ["git", "commit", "-m", msg],
        cwd=REPO_ROOT,
        check=True,
    )
    r = subprocess.run(["git", "push"], cwd=REPO_ROOT)
    if r.returncode != 0:
        print(f"  WARNING: git push failed (rc={r.returncode}), commit is local only")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    global TEST_DIR

    parser = argparse.ArgumentParser(
        description="Split standalone test files into per-LRM-clause files.",
    )
    parser.add_argument("--file", required=True, help="Full path to the input test file")
    parser.add_argument("--output-dir", required=True, help="Directory for output files")
    parser.add_argument("--dry-run", action="store_true", help="Classify only, don't write files")
    args = parser.parse_args()

    dry_run = args.dry_run
    TEST_DIR = Path(args.output_dir).resolve()
    filepath = Path(args.file).resolve()
    test_name = filepath.stem

    if not filepath.exists():
        print(f"ERROR: {filepath} not found")
        sys.exit(1)

    mode = "DRY RUN" if dry_run else "LIVE"
    print(f"=== Splitting {test_name} ({mode}) ===")

    # Stage 1: Parse
    print("Stage 1: Parsing...")
    parsed = parse_file(filepath)
    print(f"  Found {len(parsed.all_tests)} tests, {len(parsed.global_preamble)} preamble items")

    if not parsed.all_tests:
        print("ERROR: No TEST blocks found")
        sys.exit(1)

    # Stage 2: Classify
    print("Stage 2: Classifying via Claude...")
    classify_tests(parsed.all_tests)

    # Print classification table
    print("\n  Classification results:")
    print(f"  {'Test':<45} {'Prefix':<15} {'Clause':<12} {'Rationale'}")
    print(f"  {'-'*45} {'-'*15} {'-'*12} {'-'*40}")
    for t in parsed.all_tests:
        print(f"  {t.test_name:<45} {t.prefix:<15} {t.clause:<12} {t.rationale}")
    print()

    # Group by (prefix, clause); for non-lrm, sub-group by topic
    groups: dict[tuple[str, str], list[TestBlock]] = {}
    for t in parsed.all_tests:
        prefix = t.prefix or "test_non_lrm"
        clause = t.clause or "non-lrm"
        if clause == "non-lrm":
            topic = t.non_lrm_topic or "misc"
            key = (prefix, f"non-lrm:{topic}")
        else:
            key = (prefix, clause)
        groups.setdefault(key, []).append(t)

    # Stage 3: Deduplicate and resolve destinations
    print("Stage 3: Checking for duplicates...")
    lrm_titles = load_lrm_titles()
    files_to_create: list[tuple[str, str, str, list[TestBlock]]] = []  # (filename, prefix, clause, tests)
    files_to_merge: list[tuple[Path, list[TestBlock]]] = []  # (existing_path, tests)

    for (prefix, clause), tests in sorted(groups.items()):
        target_base = clause_to_filename(prefix, clause, test_name)
        existing = find_existing_tests(target_base)

        unique = [t for t in tests if t.test_name not in existing]
        dupes = [t for t in tests if t.test_name in existing]

        for d in dupes:
            print(f"  DUPLICATE: {d.test_name} already in {target_base} — dropping")

        if not unique:
            print(f"  All tests for {clause} are duplicates — skipping")
            continue

        # Check if we can merge into an existing file
        merge_path = find_merge_target(target_base)
        if merge_path:
            files_to_merge.append((merge_path, unique))
            print(f"  Merging {len(unique)} tests into {merge_path.name}")
        else:
            title = lrm_titles.get(clause, "")
            files_to_create.append((target_base, prefix, clause, unique))
            print(f"  {target_base}.cpp: {len(unique)} tests (§{clause}: {title})")

    if dry_run:
        n_total = len(files_to_create) + len(files_to_merge)
        print(f"\n=== DRY RUN complete. Would create {len(files_to_create)}, merge into {len(files_to_merge)} files. ===")
        return

    # Stage 5: Generate / merge files
    n_created = len(files_to_create)
    n_merged = len(files_to_merge)
    print(f"\nStage 5: Creating {n_created}, merging into {n_merged} files...")

    new_names: list[str] = []
    for filename, prefix, clause, tests in files_to_create:
        title = lrm_titles.get(clause, "")
        content = generate_file(
            clause, title,
            parsed.includes, parsed.using_line,
            parsed.global_preamble, tests,
        )
        outpath = TEST_DIR / f"{filename}.cpp"
        outpath.write_text(content)
        new_names.append(filename)
        print(f"  Created {filename}.cpp ({len(tests)} tests)")

    for merge_path, tests in files_to_merge:
        append_tests_to_file(merge_path, parsed.global_preamble, tests)
        print(f"  Merged {len(tests)} tests into {merge_path.name}")

    # Stage 6: Update CMakeLists.txt
    print("Stage 6: Updating CMakeLists.txt...")
    update_cmake(test_name, new_names)

    # Stage 7: Clean up and commit
    print("Stage 7: Cleaning up...")
    filepath.unlink()
    print(f"  Deleted {test_name}.cpp")
    update_standalone(test_name)
    print(f"  Removed from STANDALONE.md")

    n_total = n_created + n_merged
    print("Stage 7: Committing and pushing...")
    commit_and_push(test_name, n_total)
    print(f"\nDone! Created {n_created}, merged into {n_merged} files.")


if __name__ == "__main__":
    main()
