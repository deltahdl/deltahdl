"""End-to-end tests for test_common module."""

import subprocess
import sys
from pathlib import Path

import test_common

REPO_ROOT = test_common.REPO_ROOT


class TestModuleImport:
    """Test that test_common can be imported via subprocess."""

    def test_import_succeeds_in_subprocess(self):
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
        )
        assert result.returncode == 0, (
            f"Import failed: {result.stderr}"
        )


class TestPublicApi:
    """All public names must be accessible."""

    def test_public_names_are_accessible(self):
        """REPO_ROOT, BINARY, GREEN, RED, RESET, check_binary, and
        print_result should all be importable attributes."""
        expected_names = [
            "REPO_ROOT",
            "BINARY",
            "GREEN",
            "RED",
            "RESET",
            "check_binary",
            "print_result",
        ]
        for name in expected_names:
            assert hasattr(test_common, name), (
                f"test_common missing public name: {name}"
            )
