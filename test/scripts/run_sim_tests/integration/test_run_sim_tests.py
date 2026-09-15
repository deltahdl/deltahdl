from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest


def test_all_pass_scenario(rst: ModuleType, sim_test_tree: Path) -> None:
    with patch.object(rst, "TEST_DIR", sim_test_tree):
        pairs = rst.collect_tests()

    results = []
    for sv, expected_path in pairs:
        expected_text = expected_path.read_text().rstrip("\n")
        mock_result = MagicMock()
        mock_result.stdout = expected_text + "\n"
        mock_result.stderr = ""
        with patch.object(
            rst.subprocess, "run", return_value=mock_result
        ):
            ok, _ = rst.run_test(sv, expected_path)
        results.append(ok)

    assert results == [True, True]


def test_mixed_pass_fail_scenario(rst: ModuleType, sim_test_tree: Path) -> None:
    with patch.object(rst, "TEST_DIR", sim_test_tree):
        pairs = rst.collect_tests()

    pass_count = 0
    fail_count = 0
    for sv, expected_path in pairs:
        mock_result = MagicMock()
        mock_result.stderr = ""
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
    with patch.object(rst, "TEST_DIR", test_dir), \
         patch.object(rst, "check_binary"), \
         patch.object(rst.subprocess, "run", side_effect=fake_run):
        rst.main()


def test_all_passing_exits_zero(
    rst: ModuleType,
    sim_test_tree: Path,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    def fake_run(cmd: list[str], **_: Any) -> MagicMock:
        sv_path = cmd[1]
        expected_path = sv_path.replace(".sv", ".expected")
        with open(expected_path, encoding="utf-8") as f:
            mock = MagicMock()
            mock.stdout = f.read()
            mock.stderr = ""
        return mock

    def run() -> None:
        _run_main_with_fake(rst, sim_test_tree, fake_run)

    assert get_exit_code(run) == 0


def test_no_pairs_exits_one(
    rst: ModuleType,
    tmp_path: Path,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    def run() -> None:
        with patch.object(rst, "TEST_DIR", tmp_path), \
             patch.object(rst, "check_binary"):
            rst.main()

    assert get_exit_code(run) == 1


def test_prints_detail_on_failure(
    rst: ModuleType,
    sim_test_tree: Path,
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    def fake_run(_cmd: list[str], **_: Any) -> MagicMock:
        mock = MagicMock()
        mock.stdout = "wrong output\n"
        mock.stderr = ""
        return mock

    def run() -> None:
        _run_main_with_fake(rst, sim_test_tree, fake_run)

    get_exit_code(run)
    assert "    expected:" in capsys.readouterr().out


def test_a_malformed_exit_file_does_not_stop_the_later_cases(
    rst: ModuleType,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    (tmp_path / "bad.sv").write_text("module bad; endmodule\n")
    (tmp_path / "bad.expected").write_text("bad output\n")
    (tmp_path / "bad.exit").write_text("yes\n")
    (tmp_path / "good.sv").write_text("module good; endmodule\n")
    (tmp_path / "good.expected").write_text("good output\n")

    def fake_run(_cmd: list[str], **_: Any) -> MagicMock:
        mock = MagicMock()
        mock.stdout = "good output\n"
        mock.stderr = ""
        return mock

    def run() -> None:
        _run_main_with_fake(rst, tmp_path, fake_run)

    get_exit_code(run)
    assert "sim-tests summary: 1/2 passed, 1 failed" in capsys.readouterr().out
