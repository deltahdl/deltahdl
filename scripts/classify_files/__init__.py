"""Batch-classify multiple files by invoking classify_file per file."""

import argparse
import subprocess
import sys
from pathlib import Path

from classify_test._github import (
    fetch_issue_body,
    tick_checkbox,
    update_issue_body,
)


def _parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        prog="classify_files",
        description="Batch-classify multiple files.",
    )
    parser.add_argument(
        "--files", required=True,
        help="Comma-separated list of file paths",
    )
    parser.add_argument(
        "--issue", type=int, required=True,
        help="Master GitHub issue number to update",
    )
    parser.add_argument(
        "--output-dir", required=True,
        help="Directory for output files",
    )
    parser.add_argument(
        "--lrm", required=True,
        help="Path to IEEE 1800-2023 LRM text file",
    )
    parser.add_argument(
        "--organization", required=True,
        help="GitHub organization for the issue",
    )
    parser.add_argument(
        "--repo", required=True,
        help="GitHub repository for the issue",
    )
    parser.add_argument(
        "--max-lines", type=int, required=True,
        help="Maximum lines per output file",
    )
    return parser.parse_args()


def tick_file_checkbox(
    org: str,
    repo: str,
    issue: int,
    filename: str,
) -> None:
    """Tick a file checkbox in the master issue."""
    body = fetch_issue_body(org, repo, issue)
    body = tick_checkbox(body, filename)
    update_issue_body(org, repo, issue, body)


def _build_command(
    args: argparse.Namespace,
    file_path: str,
) -> list[str]:
    """Build the subprocess command list for classify_file."""
    return [
        sys.executable, "-m", "classify_file",
        "--file", file_path,
        "--create-issue",
        "--output-dir", args.output_dir,
        "--lrm", args.lrm,
        "--organization", args.organization,
        "--repo", args.repo,
        "--max-lines", str(args.max_lines),
    ]


def run_classify_file(
    args: argparse.Namespace,
    file_path: str,
    index: int,
    total: int,
) -> None:
    """Invoke classify_file for a single file. Exits on failure."""
    print(f"Processing file {index}/{total}: {Path(file_path).name}")
    cmd = _build_command(args, file_path)
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.stdout:
        print(result.stdout, end="")
    if result.returncode != 0:
        print(result.stderr, end="", file=sys.stderr)
        sys.exit(1)


def _run(args: argparse.Namespace) -> None:
    """Execute the batch classification."""
    file_list = [f.strip() for f in args.files.split(",")]
    total = len(file_list)
    for i, file_path in enumerate(file_list, 1):
        run_classify_file(args, file_path, i, total)
        tick_file_checkbox(
            args.organization, args.repo,
            args.issue, Path(file_path).name,
        )
    print("Done")


def main():
    """Entry point for classify_files."""
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    _run(_parse_args())
