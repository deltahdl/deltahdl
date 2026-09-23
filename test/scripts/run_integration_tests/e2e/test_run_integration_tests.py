import subprocess
from collections.abc import Callable
from pathlib import Path

_SIMULATION = "/*\n:subclause: 8.25\n:stage: simulation\n*/\nmodule m; endmodule\n"
_REJECTED = (
    "/*\n:subclause: 8.25\n:stage: elaboration\n"
    ":should_fail_because: the rule under test forbids it\n*/\n"
    "module m; endmodule\n"
)
RunRunnerMain = Callable[[str, Path, Path], subprocess.CompletedProcess[str]]


def _one_case(tmp_path: Path, text: str) -> Path:
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    (test_dir / "case.sv").write_text(text)
    return test_dir


def test_a_holding_simulation_exits_zero(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    test_dir = _one_case(tmp_path, _SIMULATION)
    binary = stub_binary(exit_code=0, stdout=":assert: (3 == 3)\n")
    result = run_runner_main("run_integration_tests", test_dir, binary)
    assert result.returncode == 0


def test_a_broken_assertion_exits_one(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    test_dir = _one_case(tmp_path, _SIMULATION)
    binary = stub_binary(exit_code=0, stdout=":assert: (3 == 4)\n")
    result = run_runner_main("run_integration_tests", test_dir, binary)
    assert result.returncode == 1


def test_a_rejection_under_the_subclause_exits_zero(
    tmp_path: Path,
    stub_binary: Callable[..., Path],
    run_runner_main: RunRunnerMain,
) -> None:
    test_dir = _one_case(tmp_path, _REJECTED)
    binary = stub_binary(exit_code=1, stderr="error: no (§8.25.1)\n")
    result = run_runner_main("run_integration_tests", test_dir, binary)
    assert result.returncode == 0


def test_a_missing_binary_exits_one(
    tmp_path: Path, run_runner_main: RunRunnerMain,
) -> None:
    test_dir = _one_case(tmp_path, _SIMULATION)
    absent = tmp_path / "absent"
    result = run_runner_main("run_integration_tests", test_dir, absent)
    assert result.returncode == 1
