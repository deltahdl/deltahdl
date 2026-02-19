"""Unit tests for test_common module."""

from pathlib import Path
from unittest.mock import MagicMock, patch

from lib import test_common


def test_repo_root_contains_scripts_dir():
    """REPO_ROOT should contain a scripts/ subdirectory."""
    scripts_dir = test_common.REPO_ROOT / "scripts"
    assert scripts_dir.is_dir(), (
        f"Expected scripts/ directory at {scripts_dir}"
    )


def test_binary_equals_expected_path():
    """BINARY should equal REPO_ROOT / build / src / deltahdl."""
    expected = test_common.REPO_ROOT / "build" / "src" / "deltahdl"
    assert test_common.BINARY == expected


class TestColorConstants:
    """Tests for color constants (GREEN, RED, RESET)."""

    def test_no_color_env_disables_colors(self, reload_no_color):
        """Setting NO_COLOR=1 should make all color constants empty."""
        mod = reload_no_color
        assert (mod.GREEN, mod.RED, mod.RESET) == ("", "", "")

    def test_ci_env_enables_colors_on_tty(self, reload_with_colors):
        """With NO_COLOR unset and CI=true and a tty, colors are ANSI."""
        mod = reload_with_colors
        assert (mod.GREEN, mod.RED, mod.RESET) == (
            "\033[32m",
            "\033[31m",
            "\033[0m",
        )


class TestCheckBinary:
    """Tests for the check_binary() function."""

    def test_exits_when_binary_missing(self):
        """check_binary() should call sys.exit(1) when binary is absent."""
        mock_binary = MagicMock(spec=Path)
        mock_binary.exists.return_value = False
        exit_code = None
        try:
            with patch("lib.test_common.BINARY", mock_binary):
                test_common.check_binary()
        except SystemExit as exc:
            exit_code = exc.code
        assert exit_code == 1

    def test_returns_normally_when_binary_exists(self):
        """check_binary() should return None when the binary is present."""
        mock_binary = MagicMock(spec=Path)
        mock_binary.exists.return_value = True
        with patch("lib.test_common.BINARY", mock_binary):
            test_common.check_binary()
            assert mock_binary.exists.called


class TestPrintResult:
    """Tests for the print_result() function."""

    def test_pass_output_contains_pass_and_name(self, capsys):
        """print_result(True, ...) should print PASS and the test name."""
        test_common.print_result(True, "my_test")
        out = capsys.readouterr().out
        assert all(s in out for s in ("PASS", "my_test"))

    def test_fail_output_contains_fail_and_name(self, capsys):
        """print_result(False, ...) should print FAIL and the test name."""
        test_common.print_result(False, "my_test")
        out = capsys.readouterr().out
        assert all(s in out for s in ("FAIL", "my_test"))
