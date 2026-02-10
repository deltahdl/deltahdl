"""Integration tests for test_common module."""

import importlib
import os
from pathlib import Path
from unittest.mock import MagicMock, patch

import test_common


class TestRunnerStartupPath:
    """Test that check_binary + print_result work together."""

    def test_startup_then_print(self, capsys):
        """Simulates a runner: check binary exists, then print results."""
        mock_binary = MagicMock(spec=Path)
        mock_binary.exists.return_value = True
        with patch("test_common.BINARY", mock_binary):
            test_common.check_binary()
        test_common.print_result(True, "startup_check")
        captured = capsys.readouterr()
        assert "PASS" in captured.out
        assert "startup_check" in captured.out


class TestColorConsistency:
    """All three color constants must be unanimously empty or non-empty."""

    def test_colors_all_empty_when_no_color(self):
        """With NO_COLOR=1, GREEN, RED, RESET must all be empty."""
        env = os.environ.copy()
        env["NO_COLOR"] = "1"
        env.pop("CI", None)
        with patch.dict(os.environ, env, clear=True):
            reloaded = importlib.reload(test_common)
            values = [reloaded.GREEN, reloaded.RED, reloaded.RESET]
            assert all(v == "" for v in values)

    def test_colors_all_nonempty_when_tty(self):
        """With a tty and no NO_COLOR, all color constants are non-empty."""
        env = os.environ.copy()
        env.pop("NO_COLOR", None)
        env["CI"] = "true"
        with patch.dict(os.environ, env, clear=True), \
             patch("sys.stdout") as mock_stdout:
            mock_stdout.isatty.return_value = True
            reloaded = importlib.reload(test_common)
            values = [reloaded.GREEN, reloaded.RED, reloaded.RESET]
            assert all(v != "" for v in values)


class TestBinaryRelativeToRoot:
    """BINARY must be relative to REPO_ROOT."""

    def test_binary_is_under_repo_root(self):
        """BINARY path should start with REPO_ROOT."""
        assert str(test_common.BINARY).startswith(str(test_common.REPO_ROOT))
