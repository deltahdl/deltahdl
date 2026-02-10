"""Integration tests for test_common module."""

from pathlib import Path
from unittest.mock import MagicMock, patch

import test_common


def test_startup_then_print(capsys):
    """Simulates a runner: check binary exists, then print results."""
    mock_binary = MagicMock(spec=Path)
    mock_binary.exists.return_value = True
    with patch("test_common.BINARY", mock_binary):
        test_common.check_binary()
    test_common.print_result(True, "startup_check")
    out = capsys.readouterr().out
    assert all(s in out for s in ("PASS", "startup_check"))


class TestColorConsistency:
    """All three color constants must be unanimously empty or non-empty."""

    def test_colors_all_empty_when_no_color(self, reload_no_color):
        """With NO_COLOR=1, GREEN, RED, RESET must all be empty."""
        mod = reload_no_color
        assert all(v == "" for v in (mod.GREEN, mod.RED, mod.RESET))

    def test_colors_all_nonempty_when_tty(self, reload_with_colors):
        """With a tty and no NO_COLOR, all color constants are non-empty."""
        mod = reload_with_colors
        assert all(v != "" for v in (mod.GREEN, mod.RED, mod.RESET))


def test_binary_is_under_repo_root():
    """BINARY path should start with REPO_ROOT."""
    assert str(test_common.BINARY).startswith(str(test_common.REPO_ROOT))
