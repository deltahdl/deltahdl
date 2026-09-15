from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch

import pytest

from lib.python import run_tests_common


def test_startup_then_print(capsys: pytest.CaptureFixture[str]) -> None:
    mock_binary = MagicMock(spec=Path)
    mock_binary.exists.return_value = True
    with patch("lib.python.run_tests_common.BINARY", mock_binary):
        run_tests_common.check_binary()
    run_tests_common.print_result(True, "startup_check")
    out = capsys.readouterr().out
    assert all(s in out for s in ("PASS", "startup_check"))


class TestColorConsistency:
    def test_colors_all_empty_when_no_color(
        self, reload_no_color: ModuleType,
    ) -> None:
        mod = reload_no_color
        assert all(v == "" for v in (mod.GREEN, mod.RED, mod.RESET))

    def test_colors_all_nonempty_when_tty(
        self, reload_with_colors: ModuleType,
    ) -> None:
        mod = reload_with_colors
        assert all(v != "" for v in (mod.GREEN, mod.RED, mod.RESET))


def test_binary_is_under_repo_root() -> None:
    assert str(run_tests_common.BINARY).startswith(str(run_tests_common.REPO_ROOT))
