import subprocess
import sys
from unittest.mock import MagicMock, patch

import pytest

from lib.python import run_tests_common

_COMMAND = ["deltahdl", "--lint-only", "two words.sv"]


def _completed(
    returncode: int, stdout: str, stderr: str,
) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(_COMMAND, returncode, stdout, stderr)


def _report_of(
    capsys: pytest.CaptureFixture[str],
    result: subprocess.CompletedProcess[str],
) -> str:
    with patch.object(subprocess, "run", return_value=result):
        run_tests_common.run_reported(_COMMAND, timeout=30)
    return capsys.readouterr().out


def _timeout_report_of(
    capsys: pytest.CaptureFixture[str],
    stdout: bytes | None,
    stderr: bytes | None,
) -> str:
    expired = subprocess.TimeoutExpired(_COMMAND, 30, stdout, stderr)
    with patch.object(
        subprocess, "run", side_effect=expired,
    ), pytest.raises(subprocess.TimeoutExpired):
        run_tests_common.run_reported(_COMMAND, timeout=30)
    return capsys.readouterr().out


def test_returns_the_completed_process() -> None:
    result = _completed(3, "out\n", "err\n")
    with patch.object(subprocess, "run", return_value=result):
        assert run_tests_common.run_reported(_COMMAND, timeout=30) is result


def test_runs_the_command_capturing_text_in_the_given_directory() -> None:
    with patch.object(
        subprocess, "run",
        return_value=_completed(0, "", ""),
    ) as run:
        run_tests_common.run_reported(_COMMAND, timeout=7, cwd="/work")
    assert run.call_args.kwargs == {
        "capture_output": True,
        "text": True,
        "timeout": 7,
        "check": False,
        "cwd": "/work",
    }


def test_reports_the_command_line_quoted(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(0, "", ""))
    assert "    $ deltahdl --lint-only 'two words.sv'\n" in out


def test_reports_the_exit_status_of_a_passing_process(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(0, "", ""))
    assert "    exit status 0\n" in out


def test_reports_the_exit_status_of_a_failing_process(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(1, "", ""))
    assert "    exit status 1\n" in out


def test_reports_every_stdout_line_indented(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(0, "first\nsecond", ""))
    assert "    stdout:\n      first\n      second\n" in out


def test_reports_every_stderr_line_indented(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(1, "", "error: a\nerror: b\n"))
    assert "    stderr:\n      error: a\n      error: b\n" in out


def test_reports_an_empty_stream_as_empty(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(0, "", "warned\n"))
    assert "    stdout: (empty)\n" in out


def test_reports_in_order_command_status_stdout_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _report_of(capsys, _completed(2, "o\n", "e\n"))
    assert out == (
        "    $ deltahdl --lint-only 'two words.sv'\n"
        "    exit status 2\n"
        "    stdout:\n      o\n"
        "    stderr:\n      e\n"
    )


def test_writes_the_report_in_one_call() -> None:
    stdout = MagicMock()
    with patch.object(
        subprocess, "run",
        return_value=_completed(0, "a\nb\n", "c\n"),
    ), patch.object(sys, "stdout", stdout):
        run_tests_common.run_reported(_COMMAND, timeout=30)
    assert stdout.write.call_count == 1


def test_flushes_after_writing_the_report() -> None:
    stdout = MagicMock()
    with patch.object(
        subprocess, "run",
        return_value=_completed(0, "", ""),
    ), patch.object(sys, "stdout", stdout):
        run_tests_common.run_reported(_COMMAND, timeout=30)
    assert [name for name, _, _ in stdout.method_calls] == ["write", "flush"]


def test_reports_a_timeout_in_place_of_the_exit_status(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _timeout_report_of(capsys, None, None)
    assert "    timed out after 30 s\n" in out


def test_reports_the_output_a_timed_out_process_wrote(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _timeout_report_of(capsys, b"partial\n", b"stuck\n")
    assert "    stdout:\n      partial\n    stderr:\n      stuck\n" in out


def test_reports_no_output_from_a_timed_out_process_as_empty(
    capsys: pytest.CaptureFixture[str],
) -> None:
    out = _timeout_report_of(capsys, None, None)
    assert "    stdout: (empty)\n    stderr: (empty)\n" in out


def test_runs_a_real_process(capsys: pytest.CaptureFixture[str]) -> None:
    run_tests_common.run_reported(
        [sys.executable, "-c", "import sys; print('hi'); sys.exit(4)"],
        timeout=30,
    )
    assert "    exit status 4\n    stdout:\n      hi\n" in capsys.readouterr().out
