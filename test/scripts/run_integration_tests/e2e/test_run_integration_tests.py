import subprocess
import sys
import textwrap
from collections.abc import Callable
from pathlib import Path

from lib.python import run_tests_common

REPO_ROOT = run_tests_common.REPO_ROOT
SCRIPTS_DIR = REPO_ROOT / "scripts"

_SIMULATION = "/*\n:subclause: 8.25\n:stage: simulation\n*/\nmodule m; endmodule\n"
_REJECTED = (
    "/*\n:subclause: 8.25\n:stage: elaboration\n"
    ":should_fail_because: the rule under test forbids it\n*/\n"
    "module m; endmodule\n"
)


def _run_script(
    test_dir: Path, binary_path: Path,
) -> subprocess.CompletedProcess[str]:
    code = textwrap.dedent(f"""\
        import sys
        sys.path.insert(0, {str(REPO_ROOT)!r})
        sys.path.insert(0, {str(SCRIPTS_DIR)!r})
        from pathlib import Path
        import run_integration_tests
        from lib.python import run_tests_common
        run_integration_tests.TEST_DIR = Path({str(test_dir)!r})
        run_tests_common.BINARY = Path({str(binary_path)!r})
        run_integration_tests.BINARY = run_tests_common.BINARY
        run_integration_tests.main()
    """)
    return subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )


def _one_case(tmp_path: Path, text: str) -> Path:
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    (test_dir / "case.sv").write_text(text)
    return test_dir


def test_a_holding_simulation_exits_zero(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    test_dir = _one_case(tmp_path, _SIMULATION)
    binary = stub_binary(exit_code=0, stdout=":assert: (3 == 3)\n")
    assert _run_script(test_dir, binary).returncode == 0


def test_a_broken_assertion_exits_one(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    test_dir = _one_case(tmp_path, _SIMULATION)
    binary = stub_binary(exit_code=0, stdout=":assert: (3 == 4)\n")
    assert _run_script(test_dir, binary).returncode == 1


def test_a_rejection_under_the_subclause_exits_zero(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    test_dir = _one_case(tmp_path, _REJECTED)
    binary = stub_binary(exit_code=1, stderr="error: no (§8.25.1)\n")
    assert _run_script(test_dir, binary).returncode == 0


def test_a_missing_binary_exits_one(tmp_path: Path) -> None:
    test_dir = _one_case(tmp_path, _SIMULATION)
    assert _run_script(test_dir, tmp_path / "absent").returncode == 1
