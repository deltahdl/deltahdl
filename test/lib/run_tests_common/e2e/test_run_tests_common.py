"""End-to-end tests for run_tests_common module."""

import subprocess
import sys

from lib import run_tests_common

REPO_ROOT = run_tests_common.REPO_ROOT


def test_import_succeeds_in_subprocess():
    """Importing run_tests_common in a fresh Python process should succeed."""
    repo_root = str(REPO_ROOT)
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            f"import sys; sys.path.insert(0, {repo_root!r}); "
            "from lib import run_tests_common",
        ],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    assert result.returncode == 0, f"Import failed: {result.stderr}"


def test_public_names_are_accessible():
    """REPO_ROOT, BINARY, GREEN, RED, RESET, check_binary, and
    print_result should all be importable attributes."""
    expected = [
        "REPO_ROOT",
        "BINARY",
        "GREEN",
        "RED",
        "RESET",
        "check_binary",
        "print_result",
    ]
    assert all(hasattr(run_tests_common, n) for n in expected)
