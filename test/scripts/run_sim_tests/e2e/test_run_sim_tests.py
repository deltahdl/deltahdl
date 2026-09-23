import subprocess
from collections.abc import Callable
from pathlib import Path

RunRunnerMain = Callable[[str, Path, Path], subprocess.CompletedProcess[str]]


def test_exit_zero_when_all_pass(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    (test_dir / "hello.sv").write_text("module hello; endmodule\n")
    (test_dir / "hello.expected").write_text("Hello, World!\n")

    binary = stub_binary(exit_code=0, stdout="Hello, World!\n")
    result = run_runner_main("run_sim_tests", test_dir, binary)

    assert result.returncode == 0


def _run_mismatching_case(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> subprocess.CompletedProcess[str]:
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    (test_dir / "bad.sv").write_text("module bad; endmodule\n")
    (test_dir / "bad.expected").write_text("expected output\n")
    binary = stub_binary(exit_code=0, stdout="wrong output\n")
    return run_runner_main("run_sim_tests", test_dir, binary)


def _run_over_a_directory_holding_no_pair(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> subprocess.CompletedProcess[str]:
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    binary = stub_binary(exit_code=0, stdout="")
    return run_runner_main("run_sim_tests", test_dir, binary)


def test_exit_one_on_mismatch(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    result = _run_mismatching_case(tmp_path, stub_binary, run_runner_main)
    assert result.returncode == 1


def test_diff_shown_on_mismatch(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    result = _run_mismatching_case(tmp_path, stub_binary, run_runner_main)
    assert "expected" in result.stdout


def test_exit_one_when_no_pairs(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    result = _run_over_a_directory_holding_no_pair(
        tmp_path, stub_binary, run_runner_main,
    )
    assert result.returncode == 1


def test_error_printed_when_no_pairs(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    result = _run_over_a_directory_holding_no_pair(
        tmp_path, stub_binary, run_runner_main,
    )
    assert "error" in result.stderr
