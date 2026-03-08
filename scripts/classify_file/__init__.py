"""Batch-classify all tests in a file by invoking classify_test per test."""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

from lib.python.git import commit_and_push
from classify_test._github import fetch_issue_body, update_issue_body
from lib.python.github import close_issue
from lib.python.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
)


_TEST_RE = re.compile(
    r"^\s*TEST(?:_[FP])?\(\s*\w+\s*,\s*(\w+)\s*\)",
    re.MULTILINE,
)


def extract_test_names(filepath: Path) -> list[str]:
    """Extract all test names from TEST/TEST_F/TEST_P blocks in a file."""
    text = filepath.read_text(encoding="utf-8")
    return _TEST_RE.findall(text)


def build_issue_body(test_names: list[str]) -> str:
    """Build the GitHub issue body with a status table for each test."""
    rows = "\n".join(
        f"| {name} | Unreviewed | |" for name in test_names
    )
    return (
        f"| Test | Status | Action |\n"
        f"|------|--------|--------|\n"
        f"{rows}\n"
    )


def create_issue(
    args: argparse.Namespace,
    test_names: list[str],
) -> int:
    """Create a GitHub issue and return its number."""
    filename = Path(args.file).name
    title = f"Classify tests in {filename}"
    body = build_issue_body(test_names)
    print(f"Creating issue for {filename}...")
    payload = json.dumps({"title": title, "body": body})
    result = subprocess.run(
        ["gh", "api",
         f"repos/{args.organization}/{args.repo}/issues",
         "-X", "POST", "--input", "-"],
        input=payload,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to create issue:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    issue_number = json.loads(result.stdout)["number"]
    print(f"Created issue #{issue_number}")
    return issue_number


def sync_issue_rows(
    args: argparse.Namespace,
    test_names: list[str],
) -> set[str]:
    """Sync issue table rows, adding missing tests. Return reviewed names."""
    body = fetch_issue_body(
        args.organization, args.repo, args.issue,
    )
    reviewed: set[str] = set()
    changed = False
    for name in test_names:
        row_re = re.compile(
            r"^\| " + re.escape(name) + r" \|([^|]*)\|[^|]*\|$",
            re.MULTILINE,
        )
        match = row_re.search(body)
        if match:
            status = match.group(1).strip()
            if status != "Unreviewed":
                reviewed.add(name)
        else:
            body = body.rstrip("\n") + f"\n| {name} | Unreviewed | |\n"
            changed = True
    if changed:
        update_issue_body(
            args.organization, args.repo, args.issue, body,
        )
    return reviewed


def _build_command(
    args: argparse.Namespace,
    test_name: str,
) -> list[str]:
    """Build the subprocess command list for classify_test."""
    cmd = [
        sys.executable, "-m", "classify_test",
        "--file", args.file,
        "--test", test_name,
        "--issue", str(args.issue),
    ]
    append_classify_cmd_flags(cmd, args)
    return cmd


def run_classify_test(
    args: argparse.Namespace,
    test_name: str,
    index: int,
    total: int,
) -> bool:
    """Invoke classify_test for a single test. Returns True on success."""
    print(f"Processing test {index}/{total}: {test_name}")
    cmd = _build_command(args, test_name)
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        return False
    return True



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
    test_names = extract_test_names(filepath)
    if not test_names:
        print(f"Deleting {filepath.name} because it contains"
              " no tests...")
        filepath.unlink()
        print(f"Deleted {filepath.name}")
        if not args.dry_run and not args.no_commit:
            commit_and_push([], [filepath], f"Delete empty {filepath.name}\n")
        _maybe_close(args, "the file has no tests")
        return
    if args.create_issue:
        args.issue = create_issue(args, test_names)
        reviewed: set[str] = set()
    else:
        reviewed = sync_issue_rows(args, test_names)
    pending = [n for n in test_names if n not in reviewed]
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
    total = len(pending)
    for i, name in enumerate(pending, 1):
        if not run_classify_test(args, name, i, total):
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
