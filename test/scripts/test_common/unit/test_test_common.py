"""Unit tests for test_common module."""

import importlib
import os
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

import test_common


class TestRepoRoot:
    """Tests for the REPO_ROOT constant."""

    def test_repo_root_contains_scripts_dir(self):
        """REPO_ROOT should contain a scripts/ subdirectory."""
        scripts_dir = test_common.REPO_ROOT / "scripts"
        assert scripts_dir.is_dir(), (
            f"Expected scripts/ directory at {scripts_dir}"
        )


class TestBinary:
    """Tests for the BINARY constant."""

    def test_binary_equals_expected_path(self):
        """BINARY should equal REPO_ROOT / build / src / deltahdl."""
        expected = test_common.REPO_ROOT / "build" / "src" / "deltahdl"
        assert test_common.BINARY == expected


class TestColorConstants:
    """Tests for color constants (GREEN, RED, RESET)."""

    def test_no_color_env_disables_colors(self):
        """Setting NO_COLOR=1 should make all color constants empty."""
        env = os.environ.copy()
        env["NO_COLOR"] = "1"
        env.pop("CI", None)
        with patch.dict(os.environ, env, clear=True):
            reloaded = importlib.reload(test_common)
            assert reloaded.GREEN == ""
            assert reloaded.RED == ""
            assert reloaded.RESET == ""

    def test_ci_env_enables_colors_on_tty(self):
        """With NO_COLOR unset and CI=true and a tty, colors are ANSI."""
        env = os.environ.copy()
        env.pop("NO_COLOR", None)
        env["CI"] = "true"
        with patch.dict(os.environ, env, clear=True), \
             patch("sys.stdout") as mock_stdout:
            mock_stdout.isatty.return_value = True
            reloaded = importlib.reload(test_common)
            assert reloaded.GREEN == "\033[32m"
            assert reloaded.RED == "\033[31m"
            assert reloaded.RESET == "\033[0m"


class TestCheckBinary:
    """Tests for the check_binary() function."""

    def test_exits_when_binary_missing(self):
        """check_binary() should call sys.exit(1) when binary is absent."""
        mock_binary = MagicMock(spec=Path)
        mock_binary.exists.return_value = False
        with patch("test_common.BINARY", mock_binary):
            with pytest.raises(SystemExit) as exc_info:
                test_common.check_binary()
            assert exc_info.value.code == 1

    def test_returns_normally_when_binary_exists(self):
        """check_binary() should return None when the binary is present."""
        mock_binary = MagicMock(spec=Path)
        mock_binary.exists.return_value = True
        with patch("test_common.BINARY", mock_binary):
            result = test_common.check_binary()
            assert result is None


class TestPrintResult:
    """Tests for the print_result() function."""

    def test_pass_output_contains_pass_and_name(self, capsys):
        """print_result(True, ...) should print PASS and the test name."""
        test_common.print_result(True, "my_test")
        captured = capsys.readouterr()
        assert "PASS" in captured.out
        assert "my_test" in captured.out

    def test_fail_output_contains_fail_and_name(self, capsys):
        """print_result(False, ...) should print FAIL and the test name."""
        test_common.print_result(False, "my_test")
        captured = capsys.readouterr()
        assert "FAIL" in captured.out
        assert "my_test" in captured.out
