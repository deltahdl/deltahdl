from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch

import pytest

ExitCode = Callable[[Callable[[], object]], int | str | None]

_SIMULATION = "/*\n:subclause: 8.25\n:stage: simulation\n*/\nmodule m; endmodule\n"


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


def _one_holding_one_failing(tmp_path: Path) -> Callable[..., MagicMock]:
    (tmp_path / "holds.sv").write_text(_SIMULATION)
    (tmp_path / "breaks.sv").write_text(_SIMULATION)
    return _stub_printing({
        "holds": ":assert: (1 == 1)\n", "breaks": ":assert: (1 == 2)\n",
    })


def test_all_holding_exits_zero(
    rit: ModuleType, tmp_path: Path, get_exit_code: ExitCode,
) -> None:
    (tmp_path / "holds.sv").write_text(_SIMULATION)
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
    get_exit_code(lambda: _run_main(rit, tmp_path, fake_run))
    assert "integration-tests summary: 1/2 passed, 1 failed" in capsys.readouterr().out


def test_a_failure_prints_its_detail_indented(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    fake_run = _one_holding_one_failing(tmp_path)
    get_exit_code(lambda: _run_main(rit, tmp_path, fake_run))
    assert "    Assertion failed: (1 == 2)" in capsys.readouterr().out


def test_a_malformed_header_does_not_stop_the_later_cases(
    rit: ModuleType,
    tmp_path: Path,
    get_exit_code: ExitCode,
    capsys: pytest.CaptureFixture[str],
) -> None:
    (tmp_path / "a_stageless.sv").write_text("/*\n:subclause: 8.25\n*/\n")
    (tmp_path / "b_holds.sv").write_text(_SIMULATION)
    fake_run = _stub_printing({"b_holds": ":assert: (1 == 1)\n"})
    get_exit_code(lambda: _run_main(rit, tmp_path, fake_run))
    assert "integration-tests summary: 1/2 passed, 1 failed" in capsys.readouterr().out


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
