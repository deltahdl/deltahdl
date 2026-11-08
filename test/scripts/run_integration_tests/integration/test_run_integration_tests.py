import re
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch

import pytest

ExitCode = Callable[[Callable[[], object]], int | str | None]

_SIMULATION = ":subclause: 8.25\n:stage: simulation\n"


def _write_case(test_dir: Path, stem: str, metadata: str) -> None:
    (test_dir / f"{stem}.sv").write_text(f"module {stem}; endmodule\n")
    (test_dir / f"{stem}.metadata").write_text(metadata)


def _stub_printing(stdout_of: dict[str, str]) -> Callable[..., MagicMock]:
    def fake_run(cmd: list[str], **_: object) -> MagicMock:
        return MagicMock(returncode=0, stdout=stdout_of[Path(cmd[-1]).stem], stderr="")

    return fake_run


def _run_main(
    rit: ModuleType, test_dir: Path, fake_run: Callable[..., MagicMock],
) -> None:
    with patch.object(rit, "TEST_DIR", test_dir), \
         patch.object(rit, "check_binary"), \
         patch.object(rit.subprocess, "run", side_effect=fake_run):
        rit.main()


def _printed(
    rit: ModuleType,
    tmp_path: Path,
    fake_run: Callable[..., MagicMock],
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> str:
    get_exit_code(lambda: _run_main(rit, tmp_path, fake_run))
    return re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)


def _one_holding_one_failing(tmp_path: Path) -> Callable[..., MagicMock]:
    _write_case(tmp_path, "holds", _SIMULATION)
    _write_case(tmp_path, "breaks", _SIMULATION)
    return _stub_printing({
        "holds": ":assert: (1 == 1)\n", "breaks": ":assert: (1 == 2)\n",
    })


def test_all_holding_exits_zero(
    rit: ModuleType, tmp_path: Path, get_exit_code: ExitCode,
) -> None:
    _write_case(tmp_path, "holds", _SIMULATION)
    fake_run = _stub_printing({"holds": ":assert: (1 == 1)\n"})
    assert get_exit_code(lambda: _run_main(rit, tmp_path, fake_run)) == 0


def test_one_failing_exits_one(
    rit: ModuleType, tmp_path: Path, get_exit_code: ExitCode,
) -> None:
    fake_run = _one_holding_one_failing(tmp_path)
    assert get_exit_code(lambda: _run_main(rit, tmp_path, fake_run)) == 1


def test_the_summary_counts_each_verdict(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_holding_one_failing(tmp_path)
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "integration-tests summary: 1/2 passed (50.0%), 1 failed" in out


def test_a_failure_prints_its_detail_indented(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_holding_one_failing(tmp_path)
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "    Assertion failed: (1 == 2)" in out


def test_a_result_is_named_by_its_subclause_and_file(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_holding_one_failing(tmp_path)
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "  PASS: 8.25--holds.sv\n" in out


def test_the_clause_table_counts_the_failures_under_the_top_clause(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_holding_one_failing(tmp_path)
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "│ 8      │      1 │" in out


def test_incomplete_metadata_does_not_stop_the_later_cases(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _write_case(tmp_path, "a_stageless", ":subclause: 8.25\n")
    _write_case(tmp_path, "b_holds", _SIMULATION)
    fake_run = _stub_printing({"b_holds": ":assert: (1 == 1)\n"})
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "integration-tests summary: 1/2 passed (50.0%), 1 failed" in out


def _one_unnumbered(tmp_path: Path) -> Callable[..., MagicMock]:
    _write_case(tmp_path, "unnumbered", ":stage: simulation\n")
    return _stub_printing({})


def test_a_result_without_a_subclause_is_named_by_its_file(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_unnumbered(tmp_path)
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "  FAIL: unnumbered.sv\n" in out


def test_a_failure_without_a_subclause_counts_under_none(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_unnumbered(tmp_path)
    out = _printed(rit, tmp_path, fake_run, get_exit_code, capsys)
    assert "│ none   │      1 │" in out


def test_a_case_without_a_metadata_file_is_named_by_its_file(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    (tmp_path / "bare.sv").write_text("module bare; endmodule\n")
    out = _printed(rit, tmp_path, _stub_printing({}), get_exit_code, capsys)
    assert "  FAIL: bare.sv\n" in out


def test_an_empty_directory_exits_one(
    rit: ModuleType, tmp_path: Path, get_exit_code: ExitCode,
) -> None:
    fake_run = _stub_printing({})
    assert get_exit_code(lambda: _run_main(rit, tmp_path, fake_run)) == 1


def test_an_empty_directory_is_reported_on_stderr(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _stub_printing({})
    get_exit_code(lambda: _run_main(rit, tmp_path, fake_run))
    assert "error: no .sv files found" in capsys.readouterr().err
