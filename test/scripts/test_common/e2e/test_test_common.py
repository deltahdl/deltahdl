"""End-to-end tests for test_common module."""

import subprocess
import sys

import test_common

REPO_ROOT = test_common.REPO_ROOT


def test_import_succeeds_in_subprocess():
    """Importing test_common in a fresh Python process should succeed."""
    scripts_dir = str(REPO_ROOT / "scripts")
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            f"import sys; sys.path.insert(0, {scripts_dir!r}); "
            "import test_common",
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
    assert all(hasattr(test_common, n) for n in expected)
