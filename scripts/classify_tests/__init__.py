"""Batch-classify selected tests in a file by invoking classify_test per test."""

import argparse
import subprocess
import sys

from lib.python.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
)


def _build_command(args, test_name):
    """Build the subprocess command list for classify_test."""
    cmd = [
        sys.executable, "-m", "classify_test",
        "--file", args.file,
        "--test", test_name,
    ]
    if args.issue is not None:
        cmd += ["--issue", str(args.issue)]
    append_classify_cmd_flags(cmd, args)
    return cmd


def run_classify_test(args, test_name, index, total):
    """Invoke classify_test for a single test. Returns True on success."""
    print(f"Processing test {index}/{total}: {test_name}")
    result = subprocess.run(_build_command(args, test_name), check=False)
    return result.returncode == 0


def _parse_args():
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
    return parser.parse_args()


def _run(args):
    """Execute the batch classification."""
    names = [n.strip() for n in args.tests.split(",")]
    total = len(names)
    for i, name in enumerate(names, 1):
        if not run_classify_test(args, name, i, total):
            sys.exit(1)


def main():
    """Entry point for classify_tests."""
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    _run(_parse_args())
