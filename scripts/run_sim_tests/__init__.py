"""Run simulation e2e tests against deltahdl."""

import os
import subprocess
import sys
from pathlib import Path

from lib.python.run_tests_common import BINARY, REPO_ROOT, check_binary, print_result

TEST_DIR = REPO_ROOT / "test" / "src" / "e2e"


def visible_output(result: subprocess.CompletedProcess[str]) -> str:
    """Return what a user running deltahdl by hand would see on their terminal.

    A .expected file records this, so it records both streams. deltahdl writes
    a design's $display output to standard output and every diagnostic to
    standard error, so reading standard output alone leaves a source the tool
    rejects producing nothing to compare: such a case passes for as long as its
    .expected file is empty, whatever the tool reported and whether it reported
    anything at all. Standard output comes first because that is the order the
    two arrive in for a design that runs, and interleaving cannot be recovered
    from two captured pipes in any case.

    The absolute path of the repository is cut out of what comes back, because
    a diagnostic names the source file it stands in and the name deltahdl is
    given is the one the caller passed. That path is
    /home/runner/work/deltahdl/deltahdl/... on the Ubuntu jobs and
    /Users/runner/work/... on macos-26, so a .expected holding it could match
    on one runner only. What is left is the path relative to the repository,
    which is the same everywhere and is how the repository names a file
    anywhere else.
    """
    combined = f"{result.stdout}{result.stderr}"
    return combined.replace(f"{REPO_ROOT}{os.sep}", "")


def collect_tests() -> list[tuple[Path, Path]]:
    """Collect all .sv files that have a matching .expected file."""
    tests: list[tuple[Path, Path]] = []
    for sv in sorted(TEST_DIR.glob("*.sv")):
        expected = sv.with_suffix(".expected")
        if expected.exists():
            tests.append((sv, expected))
    return tests


def run_test(sv_path: Path, expected_path: Path) -> tuple[bool, str]:
    """Run deltahdl on a .sv file and compare what it printed to .expected."""
    expected_text = expected_path.read_text()
    try:
        result = subprocess.run(
            [str(BINARY), str(sv_path)],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"

    actual = visible_output(result)
    if actual.rstrip("\n") == expected_text.rstrip("\n"):
        return True, ""
    return False, f"expected:\n{expected_text}got:\n{actual}"


def main() -> None:
    """Run all simulation e2e tests and print a summary."""
    check_binary()

    tests = collect_tests()
    if not tests:
        print(f"error: no test pairs found in {TEST_DIR}", file=sys.stderr)
        sys.exit(1)

    passed = 0
    failed = 0
    for sv_path, expected_path in tests:
        name = sv_path.stem
        ok, detail = run_test(sv_path, expected_path)
        print_result(ok, name)
        passed += ok
        failed += not ok
        if detail:
            for line in detail.splitlines():
                print(f"    {line}")

    total = passed + failed
    print(f"\nsim-tests summary: {passed}/{total} passed, {failed} failed")
    sys.exit(min(failed, 1))
