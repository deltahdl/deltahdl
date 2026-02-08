#!/usr/bin/env python3
"""Run CHIPS Alliance sv-tests against deltahdl (advisory)."""

import glob
import os
import subprocess
import sys
from pathlib import Path

GREEN = "\033[32m"
RED = "\033[31m"
RESET = "\033[0m"

if (not sys.stdout.isatty() and not os.environ.get("CI")) or os.environ.get(
    "NO_COLOR"
):
    GREEN = RED = RESET = ""

REPO_ROOT = Path(__file__).resolve().parent.parent
BINARY = REPO_ROOT / "build" / "src" / "deltahdl"
TEST_DIR = REPO_ROOT / "third_party" / "sv-tests" / "tests"


def collect_tests():
    """Collect all .sv files under the chapter directories."""
    pattern = str(TEST_DIR / "chapter-*" / "*.sv")
    return sorted(glob.glob(pattern))


def run_test(path):
    """Run deltahdl --lint-only on a single .sv file. Returns True on pass."""
    result = subprocess.run(
        [str(BINARY), "--lint-only", path],
        capture_output=True,
        timeout=30,
        check=False,
    )
    return result.returncode == 0


def main():
    """Run all sv-tests and print a summary."""
    if not BINARY.exists():
        print(f"error: binary not found at {BINARY}", file=sys.stderr)
        rc = 1
    elif not (tests := collect_tests()):
        print(f"error: no .sv files found in {TEST_DIR}", file=sys.stderr)
        rc = 1
    else:
        passed = 0
        failed = 0
        for path in tests:
            name = Path(path).name
            try:
                if run_test(path):
                    passed += 1
                    print(f"  {GREEN}PASS{RESET}: {name}", flush=True)
                else:
                    failed += 1
                    print(f"  {RED}FAIL{RESET}: {name}", flush=True)
            except subprocess.TimeoutExpired:
                failed += 1
                print(f"  {RED}TIMEOUT{RESET}: {name}", flush=True)

        total = passed + failed
        print(f"\nsv-tests summary: {passed}/{total} passed, {failed} failed")
        rc = min(failed, 1)

    sys.exit(rc)


if __name__ == "__main__":
    main()
