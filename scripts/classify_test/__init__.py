#!/usr/bin/env python3
"""Classify tests in a file into per-LRM-clause files.

Usage:
  python3 scripts/classify_test.py \
    --file path/to/test.cpp --output-dir path/to/out
  python3 scripts/classify_test.py \
    --file path/to/test.cpp --output-dir path/to/out --dry-run
"""

import argparse
import glob
import io
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, cast

from lib.python.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
)
from lib.python.clause import STAGE_TO_PREFIX, clause_to_filename
from lib.python.cli import add_continue_arg, run_claude_cli, run_with_dots
from ._github import (
    _validate_issue_args,
    build_action_remark,
    build_commit_url,
    maybe_update_issue_status,
    update_issue_after_commit,
)
from ._models import Classification, ParsedFile, PreambleItem, TestBlock
from ._parse import (
    _parse_body,
    _parse_header,
    _try_parse_preamble,
    _update_brace_depth,
    extract_brace_block,
    is_section_header,
    parse_file,
)
from ._generate import _filter_preamble, _preamble_name, generate_file
from ._git import commit_classification
from ._patterns import (
    CLAUSE_SCHEMA,
    PREFIX_PROMPT_TEMPLATE, PREFIX_SCHEMA, TOPIC_SCHEMA,
    build_clause_prompt, build_topic_prompt,
)
from ._output import print_classification_table
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
# Stage 2: Classify via Claude
# ---------------------------------------------------------------------------

_STAGE_TO_PREFIX = STAGE_TO_PREFIX
_PREFIX_PROMPT_TEMPLATE = PREFIX_PROMPT_TEMPLATE
_PREFIX_SCHEMA = PREFIX_SCHEMA


def _detect_prefix(test: TestBlock, clause: str, lrm_path: str) -> str:
    """Detect pipeline stage prefix from test body."""
    if clause.replace("_", "-").startswith("non-lrm"):
        test.classification.prefix_rationale = "clause is non-LRM"
        return "test_non_lrm_"
    body = "\n".join(test.lines)
    print(f"Calling Claude to detect pipeline stage for"
          f" {test.test_name}...",
          end="", flush=True)
    prompt = _PREFIX_PROMPT_TEMPLATE.format(
        lrm_path=lrm_path,
        suite=test.suite_name,
        test_name=test.test_name,
        test_body=body,
    )
    resp = _call_claude(prompt, _PREFIX_SCHEMA, continue_session=True)
    print()
    stage = resp.get("pipeline_stage", "")
    prefix = _STAGE_TO_PREFIX.get(stage)
    if prefix:
        test.classification.prefix_rationale = resp.get("rationale", "")
        return prefix
    print(f"ERROR: Cannot detect pipeline stage for test"
          f" {test.test_name}. Claude returned: {resp}")
    sys.exit(1)


def existing_non_lrm_topics(test_dir: Path) -> list[str]:
    """Scan output dir for existing test_non_lrm_*.cpp topic names."""
    topics: set[str] = set()
    pattern = str(test_dir / "test_non_lrm_*.cpp")
    for fpath in sorted(glob.glob(pattern)):
        stem = Path(fpath).stem
        topic = stem[len("test_non_lrm_"):]
        if len(topic) >= 2 and topic[-2] == "_" and topic[-1].isalpha():
            topic = topic[:-2]
        if topic:
            topics.add(topic)
    return sorted(topics)


_CLAUSE_SCHEMA = CLAUSE_SCHEMA
_TOPIC_SCHEMA = TOPIC_SCHEMA


def _build_topic_hint(test_dir: Path) -> str:
    """Build existing topics hint for non-LRM classification."""
    topics = existing_non_lrm_topics(test_dir)
    if not topics:
        return ""
    return (
        "Existing topic files: "
        + ", ".join(topics)
        + "\nPREFER reusing one of these topics when the"
        " test fits, to avoid near-duplicate filenames.\n"
    )


def _extract_json(text: str) -> Any:
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


def _call_claude(
    prompt: str,
    schema: str | None = None,
    continue_session: bool = False,
) -> Any:
    """Call Claude CLI and return parsed JSON response."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    cmd = ["claude", "-p", "--model", "opus",
           "--output-format", "json", "--dangerously-skip-permissions"]
    if continue_session:
        cmd.append("--continue")
    if schema:
        cmd.extend(["--json-schema", schema])
    delays = [5, 10]
    for attempt in range(len(delays) + 1):  # pragma: no branch
        try:
            result = run_with_dots(
                run_claude_cli, cmd, prompt, env=env, timeout=600,
            )
        except subprocess.TimeoutExpired:
            if attempt < len(delays):
                print(f"WARNING: Claude CLI timed out (attempt"
                      f" {attempt + 1}/{len(delays) + 1}),"
                      f" retrying in {delays[attempt]}s...",
                      file=sys.stderr)
                time.sleep(delays[attempt])
                continue
            print("ERROR: Claude CLI timed out after"
                  f" {len(delays) + 1} attempts", file=sys.stderr)
            sys.exit(1)
        if result.returncode != 0:
            if attempt < len(delays):
                print(f"WARNING: Claude CLI failed"
                      f" (RC={result.returncode}, attempt"
                      f" {attempt + 1}/{len(delays) + 1}),"
                      f" retrying in {delays[attempt]}s...",
                      file=sys.stderr)
                time.sleep(delays[attempt])
                continue
            print(f"ERROR: Claude CLI failed (RC={result.returncode})"
                  f" after {len(delays) + 1} attempts:"
                  f"\n{result.stderr}", file=sys.stderr)
            sys.exit(1)
        break
    raw = result.stdout.strip()
    # --output-format json wraps Claude's text in an envelope
    # with keys like "result", "session_id", etc.
    try:
        envelope = json.loads(raw)
    except json.JSONDecodeError:
        return _extract_json(raw)
    if isinstance(envelope, dict) and "structured_output" in envelope:
        return envelope["structured_output"]
    if isinstance(envelope, dict) and "result" in envelope:
        return _extract_json(envelope["result"])
    return _extract_json(raw)


def _validate_clause_response(
    response: dict[str, Any], test_name: str,
) -> None:
    """Validate Claude's clause response or exit with error."""
    if "clause" not in response:
        print(f"ERROR: Classification for test {test_name} is missing"
              " required key: clause")
        sys.exit(1)
    clause = response["clause"].lstrip("§")
    response["clause"] = clause
    if not _CLAUSE_RE.match(clause):
        print(f'ERROR: Invalid clause "{clause}" for test {test_name}.'
              "\n  Expected: numeric (6.1.2), annex (A.6.3),"
              " or non-lrm")
        sys.exit(1)


def _validate_topic_response(
    response: dict[str, Any], test_name: str,
) -> None:
    """Validate Claude's topic response or exit with error."""
    if not response.get("non_lrm_topic"):
        print(f"ERROR: Topic for test {test_name} is missing"
              " or empty. A topic is required for non-lrm tests.")
        sys.exit(1)


def _rename_test_macro(
    test: TestBlock, new_suite: str, new_name: str,
) -> None:
    """Rename both args in a test block's TEST()/TEST_F()/TEST_P() line."""
    if test.classification.original_suite_name is None:
        test.classification.original_suite_name = test.suite_name
    if test.classification.original_test_name is None:
        test.classification.original_test_name = test.test_name
    test.lines[0] = re.sub(
        r'^(TEST(?:_[FP])?)\(' + re.escape(test.suite_name)
        + r',\s*' + re.escape(test.test_name) + r'\)',
        rf'\1({new_suite}, {new_name})',
        test.lines[0],
    )
    test.suite_name = new_suite
    test.test_name = new_name


def _apply_classification(
    test: TestBlock,
    clause_resp: dict[str, Any],
    topic_resp: dict[str, Any] | None = None,
    *,
    lrm_path: str,
) -> None:
    """Apply clause and optional topic responses to a test block."""
    _validate_clause_response(clause_resp, test.test_name)
    clause = clause_resp["clause"]
    if clause.replace("_", "-") == "non-lrm":
        clause = "non-lrm"
    if clause == "non-lrm" and topic_resp:
        _validate_topic_response(topic_resp, test.test_name)
        clause = f"non-lrm:{topic_resp['non_lrm_topic']}"
    test.classification.prefix = _detect_prefix(test, clause, lrm_path)
    test.classification.clause = clause
    test.classification.rationale = clause_resp.get("rationale", "")
    resp = topic_resp or clause_resp
    suite = resp["suite_name"]
    name = resp["test_name"]
    _rename_test_macro(test, suite, name)


def classify_test_block(
    test: TestBlock,
    test_dir: Path,
    lrm_path: str,
    *,
    continue_session: bool = False,
    against: str = "",
) -> TestBlock | None:
    """Use Claude to classify a single test's prefix and clause."""
    print(f"Calling Claude to classify clause for {test.test_name}...",
          end="", flush=True)
    clause_prompt = build_clause_prompt(test, lrm_path, against=against)
    clause_resp = _call_claude(
        clause_prompt, _CLAUSE_SCHEMA,
        continue_session=continue_session,
    )
    print()
    clause = clause_resp.get("clause", "")
    if against and clause == "none":
        print(f"  Test {test.test_name} does not belong to"
              f" {against} — skipping.")
        return None
    topic_resp = None
    if clause.replace("_", "-") == "non-lrm":
        print(f"Calling Claude to classify topic for"
              f" {test.test_name} because clause is non-lrm...",
              end="", flush=True)
        topic_prompt = build_topic_prompt(test, _build_topic_hint(test_dir))
        topic_resp = _call_claude(
            topic_prompt, _TOPIC_SCHEMA,
            continue_session=True,
        )
        print()
    _apply_classification(test, clause_resp, topic_resp,
                          lrm_path=lrm_path)
    return test


# ---------------------------------------------------------------------------
# Stage 3: Deduplicate
# ---------------------------------------------------------------------------

def normalize_test_body(test: TestBlock) -> str:
    """Return a normalized string of the test body (excluding the TEST line)."""
    body_lines = test.lines[1:]
    return "\n".join(line.strip() for line in body_lines)


def find_existing_tests(
    target_base: str, test_dir: Path, exclude_path: Path | None = None,
) -> set[str]:
    """Find normalized test bodies in existing clause files."""
    existing_bodies: set[str] = set()
    patterns = [
        str(test_dir / f"{target_base}.cpp"),
        str(test_dir / f"{target_base}_[a-z].cpp"),
    ]
    for pattern in patterns:
        for fpath in glob.glob(pattern):
            if exclude_path and Path(fpath).resolve() == exclude_path.resolve():
                continue
            lines = Path(fpath).read_text(encoding="utf-8").splitlines(
                keepends=True,
            )
            i = 0
            while i < len(lines):
                if re.match(
                    r"\s*TEST(?:_[FP])?\(\w+,\s*\w+\)", lines[i],
                ):
                    blk, end = extract_brace_block(lines, i)
                    body = "\n".join(ln.rstrip("\n").strip() for ln in blk[1:])
                    existing_bodies.add(body)
                    i = end + 1
                else:
                    i += 1
    return existing_bodies


# ---------------------------------------------------------------------------
# Stage 4: Resolve filenames
# ---------------------------------------------------------------------------

def find_merge_target(
    target_base: str, test_dir: Path, exclude_path: Path | None = None,
) -> Path | None:
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
# Stage 5: Generate files (in _generate.py, imported at top of module)
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 6: Update CMakeLists.txt
# ---------------------------------------------------------------------------

def update_cmake(
    old_name: str, new_names: list[str], *, keep_old: bool = False,
) -> None:
    """Update CMakeLists.txt: remove old entry, add new entries sorted."""
    text = CMAKE_PATH.read_text(encoding="utf-8")
    lines = text.splitlines()
    header_lines: list[str] = []
    test_names: list[str] = []
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

def _parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Split standalone test files into per-clause files.",
    )
    parser.add_argument(
        "--file", required=True, help="Path to the input test file",
    )
    add_output_args(parser)
    parser.add_argument(
        "--suite", required=True,
        help="Name of the test suite (first arg of TEST macro)",
    )
    parser.add_argument(
        "--test", required=True,
        help="Name of the single test to classify",
    )
    parser.add_argument("--issue", type=int,
                        help="GitHub issue number to update")
    add_github_args(parser)
    add_run_mode_args(parser)
    add_continue_arg(parser)
    parser.add_argument(
        "--against", default="",
        help="Comma-separated subclauses to classify against",
    )
    return parser.parse_args()


def _group_tests(
    tests: list[TestBlock],
) -> dict[tuple[str, str], list[TestBlock]]:
    """Group tests by (prefix, clause)."""
    groups: dict[tuple[str, str], list[TestBlock]] = {}
    for t in tests:
        prefix = t.classification.prefix or "test_non_lrm"
        clause = t.classification.clause or "non-lrm"
        groups.setdefault((prefix, clause), []).append(t)
    return groups


def _report_removals(
    tests: list[TestBlock],
    existing_bodies: set[str],
    target: str,
    dry_run: bool,
) -> int:
    """Print removal messages for duplicate tests and return count."""
    verb = "Would have removed" if dry_run else "Removed"
    count = 0
    for t in tests:
        if normalize_test_body(t) in existing_bodies:
            count += 1
            print(f"  - {verb} {t.test_name}() because it"
                  f" belongs in {target}.cpp where it"
                  " already exists.")
    return count


def _resolve_destinations(
    groups: dict[tuple[str, str], list[TestBlock]],
    test_dir: Path,
    exclude_path: Path | None = None,
    dry_run: bool = False,
) -> tuple[
    list[tuple[str, str, list[TestBlock]]],
    list[tuple[Path, list[TestBlock]]],
    int,
]:
    """Deduplicate tests and resolve create/merge destinations."""
    to_create: list[tuple[str, str, list[TestBlock]]] = []
    to_merge: list[tuple[Path, list[TestBlock]]] = []
    n_removed = 0
    for (prefix, clause), tests in sorted(groups.items()):
        target = clause_to_filename(prefix, clause)
        existing = find_existing_tests(target, test_dir, exclude_path)
        unique = [t for t in tests
                  if normalize_test_body(t) not in existing]
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


def _write_creates(
    to_create: list[tuple[str, str, list[TestBlock]]],
    parsed: ParsedFile,
    test_dir: Path,
    lrm_titles: dict[str, str],
    max_lines: int | None,
) -> list[str]:
    """Write newly created clause files and return their names."""
    names: list[str] = []
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


def _write_files(
    to_create: list[tuple[str, str, list[TestBlock]]],
    to_merge: list[tuple[Path, list[TestBlock]]],
    parsed: ParsedFile,
    ctx: dict[str, Any],
) -> list[str]:
    """Write new files and merge into existing files."""
    new_names = _write_creates(
        to_create, parsed, ctx["test_dir"],
        ctx["lrm_titles"], ctx.get("max_lines"),
    )
    for merge_path, tests in to_merge:
        filtered = _filter_preamble(
            parsed.global_preamble + parsed.section_preamble, tests,
        )
        split_names = append_tests_to_file(
            merge_path, filtered, tests,
            max_lines=ctx.get("max_lines"),
        )
        new_names.extend(split_names)
    return new_names


def _rewrite_source(
    filepath: Path,
    groups: dict[tuple[str, str], list[TestBlock]],
    parsed: ParsedFile,
    lrm_titles: dict[str, str],
    test_name: str,
) -> int:
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


def _validate_input(
    filepath: Path, suite_name: str, test_name: str,
) -> tuple[ParsedFile, TestBlock]:
    """Parse and validate the input file, returning (parsed, target)."""
    if not filepath.exists():
        print(f"ERROR: {filepath} not found")
        sys.exit(1)
    parsed = parse_file(filepath)
    if not parsed.all_tests:
        print("ERROR: No TEST blocks found")
        sys.exit(1)
    matches = [t for t in parsed.all_tests
               if t.suite_name == suite_name and t.test_name == test_name]
    if not matches:
        print(f"ERROR: Test {suite_name}.{test_name!r} not found"
              f" in {filepath.name}")
        sys.exit(1)
    return parsed, matches[0]


def _update_source(
    filepath: Path, parsed: ParsedFile, ctx: dict[str, Any],
) -> int:
    """Rewrite or remove the source file after moving a test."""
    others = [t for t in parsed.all_tests
              if not ((t.classification.original_suite_name
                       or t.suite_name) == ctx["suite"]
                      and (t.classification.original_test_name
                           or t.test_name) == ctx["test"])]
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
        print(f"Deleting {filepath.name} because all its tests were moved elsewhere")
        filepath.unlink()
    return 0


def _apply_rename_in_place(
    args: argparse.Namespace,
    filepath: Path,
    parsed: ParsedFile,
    target: list[TestBlock],
    action: str = "",
) -> str | None:
    """Rewrite the source file when a test is renamed but stays in place.

    Returns the commit SHA if a rename was applied, ``None`` if no
    renames were needed, or ``False`` when ``no_commit`` is set.
    """
    has_renames = any(
        (t.classification.original_test_name is not None
         and t.classification.original_test_name != t.test_name)
        or (t.classification.original_suite_name is not None
            and t.classification.original_suite_name != t.suite_name)
        for t in target
    )
    if not has_renames:
        return None
    content = generate_file(
        target[0].classification.clause or "non-lrm",
        "", parsed, parsed.all_tests,
    )
    filepath.write_text(content, encoding="utf-8")
    if not getattr(args, "no_commit", False):
        return commit_classification({
            "filepath": filepath, "target": target,
            "to_merge": [], "new_names": [],
            "test_dir": Path(args.output_dir).resolve(),
            "cmake_path": CMAKE_PATH,
            "action": action,
        })
    return None


def _build_action(
    target: list[TestBlock], source_is_target: bool,
) -> tuple[str, dict[str, str]]:
    """Build the action string and target filenames map."""
    target_filenames = {
        t.test_name: clause_to_filename(
            t.classification.prefix or "test_non_lrm_",
            t.classification.clause or "non-lrm",
        ) + ".cpp"
        for t in target
    }
    action = build_action_remark(
        target[0],
        source_is_target=source_is_target,
        target_filename=target_filenames.get(target[0].test_name, ""),
    )
    print(f"  Action: {action}")
    return action, target_filenames


def _print_destinations(
    to_create: list[tuple[str, str, list[TestBlock]]],
    to_merge: list[tuple[Path, list[TestBlock]]],
    max_lines: int | None,
) -> None:
    """Print target and merge info for resolved destinations."""
    for dest, _, _ in to_create:
        print(f"  Target: {dest}.cpp")
    for merge_into, merge_tests in to_merge:
        for t in merge_tests:
            print(f"  Merging test {t.test_name} into {merge_into.name}"
                  " because that's where it belongs and because adding"
                  " it to that file would not increase the file's"
                  f" number of lines to more than {max_lines} lines")


def _run(args: argparse.Namespace) -> None:
    """Execute the split operation."""
    _validate_issue_args(args)
    filepath = Path(args.file).resolve()
    parsed, target = _validate_input(filepath, args.suite, args.test)
    out_dir = Path(args.output_dir).resolve()
    if classify_test_block(
        target, out_dir,
        str(Path(args.lrm).resolve()),
        continue_session=args.continue_session,
        against=args.against,
    ) is None:
        return
    targets = [target]
    print_classification_table(targets)
    groups = _group_tests(targets)
    source_is_target = any(
        clause_to_filename(p, c) == filepath.stem
        for p, c in groups
    )
    action, target_filenames = _build_action(targets, source_is_target)
    to_create, to_merge, n_removed = _resolve_destinations(
        groups, out_dir,
        exclude_path=filepath, dry_run=args.dry_run,
    )
    _print_destinations(to_create, to_merge, args.max_lines)
    if args.dry_run:
        return
    if not to_create and not to_merge and source_is_target and n_removed == 0:
        sha = _apply_rename_in_place(args, filepath, parsed, targets,
                                     action)
        update_issue_after_commit(args, targets, source_is_target,
                                 target_filenames,
                                 build_commit_url(args, sha))
        return
    new_names = _write_files(to_create, to_merge, parsed, {
        "test_dir": out_dir,
        "lrm_titles": {},
        "max_lines": getattr(args, "max_lines", None),
    })
    _update_source(filepath, parsed, {
        "suite": args.suite, "test": args.test, "groups": groups,
        "titles": {}, "stem": filepath.stem,
        "source_is_target": source_is_target,
    })
    print("Updating `CMakeLists.txt` because the test moved to a new file...")
    update_cmake(
        filepath.stem, new_names,
        keep_old=source_is_target or any(
            not ((t.classification.original_suite_name
                  or t.suite_name) == args.suite
                 and (t.classification.original_test_name
                      or t.test_name) == args.test)
            for t in parsed.all_tests
        ),
    )
    print("Updated `CMakeLists.txt`")
    sha = None
    if not getattr(args, "no_commit", False):
        sha = commit_classification({
            "filepath": filepath, "target": targets,
            "to_merge": to_merge, "new_names": new_names,
            "test_dir": out_dir, "cmake_path": CMAKE_PATH,
            "action": action,
        })
    update_issue_after_commit(args, targets, source_is_target,
                              target_filenames,
                              build_commit_url(args, sha))


def main() -> None:
    """Entry point."""
    cast(io.TextIOWrapper, sys.stdout).reconfigure(line_buffering=True)
    cast(io.TextIOWrapper, sys.stderr).reconfigure(line_buffering=True)
    _run(_parse_args())


if __name__ == "__main__":  # pragma: no cover
    main()
