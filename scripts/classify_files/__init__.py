"""Batch-classify multiple files by invoking classify_file per file."""

import argparse
import re
import subprocess
import sys
from pathlib import Path

from classify_test._github import (
    fetch_issue_body,
    remove_checkbox,
    update_issue_body,
)
from lib.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
)
from lib.github import fetch_issue_title

_TITLE_RE = re.compile(r"^Classify tests in (.+)$")


def _parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        prog="classify_files",
        description="Batch-classify multiple files.",
    )
    source_group = parser.add_mutually_exclusive_group(required=True)
    source_group.add_argument(
        "--files",
        help="Comma-separated list of file paths",
    )
    source_group.add_argument(
        "--sub-issues",
        help="Comma-separated list of sub-issue numbers",
    )
    parser.add_argument(
        "--issue", type=int, required=True,
        help="Master GitHub issue number to update",
    )
    add_output_args(parser)
    add_github_args(parser)
    add_run_mode_args(parser)
    return parser.parse_args()


def extract_filename_from_title(title: str) -> str:
    """Extract filename from an issue title like 'Classify tests in X'."""
    match = _TITLE_RE.match(title)
    if not match:
        print(f"ERROR: Cannot extract filename from"
              f" title: {title!r}", file=sys.stderr)
        sys.exit(1)
    return match.group(1)


def resolve_sub_issues(
    args: argparse.Namespace,
) -> list[tuple[str, int | None]]:
    """Map sub-issue numbers to (file_path, issue_number) pairs."""
    issues = [int(n.strip()) for n in args.sub_issues.split(",")]
    entries: list[tuple[str, int | None]] = []
    for issue in issues:
        print(f"Fetching title for issue #{issue}...")
        title = fetch_issue_title(
            args.organization, args.repo, issue,
        )
        filename = extract_filename_from_title(title)
        file_path = str(Path(args.output_dir) / filename)
        entries.append((file_path, issue))
    return entries


def remove_file_checkbox(
    org: str,
    repo: str,
    issue: int,
    filename: str,
) -> None:
    """Remove a file checkbox from the master issue."""
    print(f"Removing {filename} from issue #{issue}...")
    body = fetch_issue_body(org, repo, issue)
    try:
        body = remove_checkbox(body, filename)
    except ValueError:
        print(f"Filename not found in issue #{issue}."
              " Nothing to delete.")
        return
    update_issue_body(org, repo, issue, body)


def _build_command(
    args: argparse.Namespace,
    file_path: str,
    *,
    sub_issue: int | None = None,
) -> list[str]:
    """Build the subprocess command list for classify_file."""
    cmd = [
        sys.executable, "-m", "classify_file",
        "--file", file_path,
    ]
    if sub_issue is not None:
        cmd += ["--issue", str(sub_issue)]
    else:
        cmd.append("--create-issue")
    append_classify_cmd_flags(cmd, args)
    return cmd


def run_classify_file(
    args: argparse.Namespace,
    file_path: str,
    index: int,
    total: int,
    *,
    sub_issue: int | None = None,
) -> None:
    """Invoke classify_file for a single file. Exits on failure."""
    print(f"Processing file {index}/{total}: {Path(file_path).name}")
    cmd = _build_command(args, file_path, sub_issue=sub_issue)
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(1)


def _run(args: argparse.Namespace) -> None:
    """Execute the batch classification."""
    if args.sub_issues is not None:
        entries = resolve_sub_issues(args)
    else:
        entries = [(f.strip(), None) for f in args.files.split(",")]
    total = len(entries)
    for i, (file_path, sub_issue) in enumerate(entries, 1):
        run_classify_file(
            args, file_path, i, total, sub_issue=sub_issue,
        )
        if not Path(file_path).exists():
            remove_file_checkbox(
                args.organization, args.repo,
                args.issue, Path(file_path).name,
            )
    print("Done")


def main():
    """Entry point for classify_files."""
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    _run(_parse_args())
