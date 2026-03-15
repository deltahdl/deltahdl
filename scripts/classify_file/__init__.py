"""Batch-classify all tests in a file by invoking classify_test per test."""

import argparse
import re
import subprocess
import sys
from pathlib import Path

from lib.python.github import (
    create_issue as _create_gh_issue,
    fetch_issue_body,
    update_issue_body,
)
from lib.python.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
)
from lib.python.git import commit_and_push
from lib.python.github import close_issue


_TEST_RE = re.compile(
    r"^\s*TEST(?:_[FP])?\(\s*(\w+)\s*,\s*(\w+)\s*\)",
    re.MULTILINE,
)


def extract_tests(filepath: Path) -> list[tuple[str, str]]:
    """Extract all (suite, test) pairs from TEST/TEST_F/TEST_P blocks."""
    text = filepath.read_text(encoding="utf-8")
    return _TEST_RE.findall(text)


def build_issue_body(test_pairs: list[tuple[str, str]]) -> str:
    """Build the GitHub issue body with a status table for each test."""
    rows = "\n".join(
        f"| {suite} | {name} | Unreviewed | |"
        for suite, name in test_pairs
    )
    return (
        f"| Suite | Test | Status | Action |\n"
        f"|-------|------|--------|--------|\n"
        f"{rows}\n"
    )


def create_issue(
    args: argparse.Namespace,
    test_pairs: list[tuple[str, str]],
) -> int:
    """Create a GitHub issue for classifying tests and return its number."""
    filename = Path(args.file).name
    title = f"Classify tests in {filename}"
    body = build_issue_body(test_pairs)
    return _create_gh_issue(args.organization, args.repo, title, body)


def _parse_existing_rows(
    body: str, test_pairs: list[tuple[str, str]],
) -> dict[str, tuple[str, str]]:
    """Extract status and action for each test in *test_pairs* from *body*."""
    existing: dict[str, tuple[str, str]] = {}
    for _suite, name in test_pairs:
        row_re = re.compile(
            r"^\|[^|]*\| " + re.escape(name)
            + r" \|([^|]*)\|([^|]*)\|$",
            re.MULTILINE,
        )
        match = row_re.search(body)
        if match:
            existing[name] = (
                match.group(1).strip(), match.group(2).strip(),
            )
    return existing


def sync_issue_rows(
    args: argparse.Namespace,
    test_pairs: list[tuple[str, str]],
) -> set[str]:
    """Rebuild issue table to match *test_pairs*. Return reviewed names."""
    body = fetch_issue_body(
        args.organization, args.repo, args.issue,
    )
    existing = _parse_existing_rows(body, test_pairs)
    reviewed: set[str] = set()
    rows: list[str] = []
    for suite, name in test_pairs:
        if name in existing:
            status, action = existing[name]
            if status != "Unreviewed":
                reviewed.add(name)
            action_cell = f" {action} " if action else " "
            rows.append(
                f"| {suite} | {name} | {status} |{action_cell}|",
            )
        else:
            rows.append(f"| {suite} | {name} | Unreviewed | |")
    header = build_issue_body(test_pairs).split("\n", 2)
    new_body = header[0] + "\n" + header[1] + "\n"
    new_body += "\n".join(rows) + "\n"
    if new_body != body:
        update_issue_body(
            args.organization, args.repo, args.issue, new_body,
        )
    return reviewed


def _build_command(
    args: argparse.Namespace,
    test_pairs: list[tuple[str, str]],
) -> list[str]:
    """Build the subprocess command list for classify_tests."""
    cmd = [
        sys.executable, "-m", "classify_tests",
        "--file", args.file,
        "--tests", ",".join(f"{s}.{n}" for s, n in test_pairs),
        "--issue", str(args.issue),
    ]
    append_classify_cmd_flags(cmd, args)
    cmd.append("--continue")
    return cmd


def run_classify_tests(
    args: argparse.Namespace,
    test_pairs: list[tuple[str, str]],
) -> bool:
    """Invoke classify_tests for a list of tests. Returns True on success."""
    cmd = _build_command(args, test_pairs)
    result = subprocess.run(cmd, check=False)
    return result.returncode == 0



def _parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        prog="classify_file",
        description="Batch-classify all tests in a file.",
    )
    parser.add_argument(
        "--file", required=True,
        help="Path to the input test file",
    )
    add_output_args(parser)
    issue_group = parser.add_mutually_exclusive_group(required=True)
    issue_group.add_argument(
        "--issue", type=int,
        help="GitHub issue number to update",
    )
    issue_group.add_argument(
        "--create-issue", action="store_true", default=False,
        help="Create a new GitHub issue for tracking",
    )
    add_github_args(parser)
    add_run_mode_args(parser)
    return parser.parse_args()


def _maybe_close(args, reason):
    """Close the issue if one is attached and not creating a new one."""
    if not args.create_issue and args.issue is not None:
        close_issue(
            args.organization, args.repo, args.issue, reason,
        )


def _run(args: argparse.Namespace) -> None:
    """Execute the batch classification."""
    filepath = Path(args.file)
    if not filepath.is_file():
        print(f"Skipping: {filepath} not found")
        _maybe_close(args, "the source file no longer exists")
        return
    test_pairs = extract_tests(filepath)
    if not test_pairs:
        print(f"Deleting {filepath.name} because it contains"
              " no tests...")
        filepath.unlink()
        print(f"Deleted {filepath.name}")
        if not args.dry_run and not args.no_commit:
            commit_and_push([], [filepath], f"Delete empty {filepath.name}\n")
        _maybe_close(args, "the file has no tests")
        return
    if args.create_issue:
        args.issue = create_issue(args, test_pairs)
        reviewed: set[str] = set()
    else:
        reviewed = sync_issue_rows(args, test_pairs)
    pending = [(s, n) for s, n in test_pairs if n not in reviewed]
    if reviewed:
        print(f"Skipping {len(reviewed)} already-reviewed"
              f" test(s): {', '.join(reviewed)}")
    if not pending:
        if not args.dry_run:
            close_issue(
                args.organization, args.repo, args.issue,
                "all tests have been classified",
            )
        return
    if not run_classify_tests(args, pending):
        sys.exit(1)
    if not args.dry_run:
        close_issue(
            args.organization, args.repo, args.issue,
            "all tests have been classified",
        )


def main():
    """Entry point for classify_file."""
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    _run(_parse_args())
