"""Integration tests for run_sim_tests module."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest


class TestCollectAndRunPipeline:
    """Tests for the collect_tests() -> run_test() pipeline."""

    def test_all_pass_scenario(
        self, rst: ModuleType, sim_test_tree: Path,
    ) -> None:
        """All tests passing should yield correct pass/fail counts."""
        with patch.object(rst, "TEST_DIR", sim_test_tree):
            pairs = rst.collect_tests()

        results = []
        for sv, expected_path in pairs:
            expected_text = expected_path.read_text().rstrip("\n")
            mock_result = MagicMock()
            mock_result.stdout = expected_text + "\n"
            with patch.object(
                rst.subprocess, "run", return_value=mock_result
            ):
                ok, _ = rst.run_test(sv, expected_path)
            results.append(ok)

        assert all(results) and len(results) == 2

    def test_mixed_pass_fail_scenario(
        self, rst: ModuleType, sim_test_tree: Path,
    ) -> None:
        """Mixed results should report correct counts."""
        with patch.object(rst, "TEST_DIR", sim_test_tree):
            pairs = rst.collect_tests()

        pass_count = 0
        fail_count = 0
        for sv, expected_path in pairs:
            mock_result = MagicMock()
            if sv.stem == "hello":
                mock_result.stdout = "Hello, World!\n"
            else:
                mock_result.stdout = "wrong output\n"
            with patch.object(
                rst.subprocess, "run", return_value=mock_result
            ):
                ok, _ = rst.run_test(sv, expected_path)
            pass_count += ok
            fail_count += not ok

        assert (pass_count, fail_count) == (1, 1)


def _run_main_with_fake(
    rst: ModuleType,
    test_dir: Path,
    fake_run: Callable[..., MagicMock],
) -> None:
    """Run rst.main() with TEST_DIR, check_binary, and subprocess.run patched."""
    with patch.object(rst, "TEST_DIR", test_dir), \
         patch.object(rst, "check_binary"), \
         patch.object(rst.subprocess, "run", side_effect=fake_run):
        rst.main()


class TestMain:
    """Tests for the main() function."""

    def test_all_passing_exits_zero(
        self,
        rst: ModuleType,
        sim_test_tree: Path,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() should call sys.exit(0) when all tests pass."""

        def fake_run(cmd: list[str], **_: Any) -> MagicMock:
            sv_path = cmd[1]
            expected_path = sv_path.replace(".sv", ".expected")
            with open(expected_path, encoding="utf-8") as f:
                mock = MagicMock()
                mock.stdout = f.read()
            return mock

        def run() -> None:
            _run_main_with_fake(rst, sim_test_tree, fake_run)

        assert get_exit_code(run) == 0

    def test_no_pairs_exits_one(
        self,
        rst: ModuleType,
        tmp_path: Path,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() should exit 1 when no .sv/.expected pairs exist."""

        def run() -> None:
            with patch.object(rst, "TEST_DIR", tmp_path), \
                 patch.object(rst, "check_binary"):
                rst.main()

        assert get_exit_code(run) == 1

    def test_prints_detail_on_failure(
        self,
        rst: ModuleType,
        sim_test_tree: Path,
        capsys: pytest.CaptureFixture[str],
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() should print indented detail lines when a test fails."""

        def fake_run(_cmd: list[str], **_: Any) -> MagicMock:
            mock = MagicMock()
            mock.stdout = "wrong output\n"
            return mock

        def run() -> None:
            _run_main_with_fake(rst, sim_test_tree, fake_run)

        get_exit_code(run)
        assert "    expected:" in capsys.readouterr().out
