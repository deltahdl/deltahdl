"""Run simulation e2e tests against deltahdl."""

import subprocess
import sys
from pathlib import Path

from lib.python.run_tests_common import BINARY, REPO_ROOT, check_binary, print_result

TEST_DIR = REPO_ROOT / "test" / "src" / "e2e"


def collect_tests() -> list[tuple[Path, Path]]:
    """Collect all .sv files that have a matching .expected file."""
    tests: list[tuple[Path, Path]] = []
    for sv in sorted(TEST_DIR.glob("*.sv")):
        expected = sv.with_suffix(".expected")
        if expected.exists():
            tests.append((sv, expected))
    return tests


def run_test(sv_path: Path, expected_path: Path) -> tuple[bool, str]:
    """Run deltahdl on a .sv file and compare output to .expected."""
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

    actual = result.stdout
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
