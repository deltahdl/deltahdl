"""Batch-classify selected tests in a file by invoking classify_test per test."""

import argparse
import io
import subprocess
import sys
from typing import cast

from lib.python.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
)
from lib.python.cli import add_continue_arg


def _build_command(
    args: argparse.Namespace,
    test_entry: str,
    *,
    continue_session: bool = False,
) -> list[str]:
    """Build the subprocess command list for classify_test."""
    suite, test = test_entry.split(".", 1)
    cmd = [
        sys.executable, "-m", "classify_test",
        "--file", args.file,
        "--suite", suite,
        "--test", test,
    ]
    if args.issue is not None:
        cmd += ["--issue", str(args.issue)]
    append_classify_cmd_flags(cmd, args)
    if continue_session:
        cmd.append("--continue")
    return cmd


def run_classify_test(
    args: argparse.Namespace,
    test_name: str,
    index: int,
    total: int,
    *,
    continue_session: bool = False,
) -> bool:
    """Invoke classify_test for a single test. Returns True on success."""
    print(f"Processing test {index}/{total}: {test_name}")
    cmd = _build_command(
        args, test_name, continue_session=continue_session,
    )
    result = subprocess.run(cmd, check=False)
    return result.returncode == 0


def _parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        prog="classify_tests",
        description="Batch-classify selected tests in a file.",
    )
    parser.add_argument(
        "--file", required=True,
        help="Path to the input test file",
    )
    parser.add_argument(
        "--tests", required=True,
        help="Comma-separated test names to classify",
    )
    parser.add_argument(
        "--issue", type=int, default=None,
        help="GitHub issue number to update",
    )
    add_output_args(parser)
    add_github_args(parser)
    add_run_mode_args(parser)
    add_continue_arg(parser)
    return parser.parse_args()


def _run(args: argparse.Namespace) -> None:
    """Execute the batch classification."""
    names = [n.strip() for n in args.tests.split(",")]
    total = len(names)
    for i, name in enumerate(names, 1):
        use_continue = i > 1 and args.continue_session
        if not run_classify_test(args, name, i, total,
                                 continue_session=use_continue):
            sys.exit(1)


def main() -> None:
    """Entry point for classify_tests."""
    cast(io.TextIOWrapper, sys.stdout).reconfigure(line_buffering=True)
    cast(io.TextIOWrapper, sys.stderr).reconfigure(line_buffering=True)
    _run(_parse_args())
