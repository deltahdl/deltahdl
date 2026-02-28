"""Batch-classify all tests in a file by invoking classify_test per test."""

import argparse
import re
import subprocess
import sys
from pathlib import Path


_TEST_RE = re.compile(
    r"^\s*TEST(?:_[FP])?\(\s*\w+\s*,\s*(\w+)\s*\)",
    re.MULTILINE,
)


def extract_test_names(filepath: Path) -> list[str]:
    """Extract all test names from TEST/TEST_F/TEST_P blocks in a file."""
    text = filepath.read_text(encoding="utf-8")
    return _TEST_RE.findall(text)


def _build_command(
    args: argparse.Namespace,
    test_name: str,
) -> list[str]:
    """Build the subprocess command list for classify_test."""
    cmd = [
        sys.executable, "-m", "classify_test",
        "--file", args.file,
        "--output-dir", args.output_dir,
        "--lrm", args.lrm,
        "--test", test_name,
    ]
    if args.issue is not None:
        cmd.extend(["--issue", str(args.issue)])
    if args.organization is not None:
        cmd.extend(["--organization", args.organization])
    if args.repo is not None:
        cmd.extend(["--repo", args.repo])
    if args.dry_run:
        cmd.append("--dry-run")
    if args.no_commit:
        cmd.append("--no-commit")
    if args.max_lines is not None:
        cmd.extend(["--max-lines", str(args.max_lines)])
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
        return False
    return True


def print_summary(
    succeeded: int,
    failed: int,
    failed_names: list[str],
) -> None:
    """Print final summary of batch classification."""
    total = succeeded + failed
    print(f"\n{succeeded}/{total} tests succeeded")
    if failed_names:
        print("Failed:")
        for name in failed_names:
            print(f"  - {name}")


def _parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Batch-classify all tests in a file.",
    )
    parser.add_argument(
        "--file", required=True,
        help="Path to the input test file",
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
        "--issue", type=int, default=None,
        help="GitHub issue number to update",
    )
    parser.add_argument(
        "--organization", default=None,
        help="GitHub organization for the issue",
    )
    parser.add_argument(
        "--repo", default=None,
        help="GitHub repository for the issue",
    )
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Classify only, don't write files",
    )
    parser.add_argument(
        "--no-commit", action="store_true",
        help="Skip git commit and push",
    )
    parser.add_argument(
        "--max-lines", type=int, default=None,
        help="Maximum lines per output file",
    )
    return parser.parse_args()


def _run(args: argparse.Namespace) -> None:
    """Execute the batch classification."""
    filepath = Path(args.file)
    if not filepath.exists():
        print(f"ERROR: {filepath} not found")
        sys.exit(1)
    test_names = extract_test_names(filepath)
    if not test_names:
        print("ERROR: No TEST blocks found")
        sys.exit(1)
    total = len(test_names)
    succeeded = 0
    failed = 0
    failed_names: list[str] = []
    for i, name in enumerate(test_names, 1):
        if run_classify_test(args, name, i, total):
            succeeded += 1
        else:
            failed += 1
            failed_names.append(name)
    print_summary(succeeded, failed, failed_names)
    if failed:
        sys.exit(1)


def main():
    """Entry point for classify_file."""
    sys.stdout.reconfigure(line_buffering=True)
    sys.stderr.reconfigure(line_buffering=True)
    _run(_parse_args())
