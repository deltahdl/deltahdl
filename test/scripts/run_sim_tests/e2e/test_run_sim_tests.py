"""End-to-end tests for run_sim_tests module."""

import subprocess
import sys
import textwrap
from collections.abc import Callable
from pathlib import Path

from lib.python import run_tests_common

REPO_ROOT = run_tests_common.REPO_ROOT
SCRIPTS_DIR = REPO_ROOT / "scripts"


def _run_sim_script(
    test_dir: Path, binary_path: Path,
) -> subprocess.CompletedProcess[str]:
    """Run run_sim_tests.main() in a subprocess with patched paths.

    Args:
        test_dir: Path to the directory containing .sv/.expected pairs.
        binary_path: Path to the stub binary to use.

    Returns:
        subprocess.CompletedProcess with stdout, stderr, and returncode.
    """
    code = textwrap.dedent(f"""\
        import sys
        sys.path.insert(0, {str(REPO_ROOT)!r})
        sys.path.insert(0, {str(SCRIPTS_DIR)!r})
        from pathlib import Path
        import run_sim_tests
        from lib.python import run_tests_common
        run_sim_tests.TEST_DIR = Path({str(test_dir)!r})
        run_tests_common.BINARY = Path({str(binary_path)!r})
        run_sim_tests.BINARY = run_tests_common.BINARY
        run_sim_tests.main()
    """)
    return subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )


def test_exit_zero_when_all_pass(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    """Script should exit 0 when stub binary echoes expected output."""
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    (test_dir / "hello.sv").write_text("module hello; endmodule\n")
    (test_dir / "hello.expected").write_text("Hello, World!\n")

    binary = stub_binary(exit_code=0, stdout="Hello, World!\n")
    result = _run_sim_script(test_dir, binary)

    assert result.returncode == 0


def _run_mismatching_case(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> subprocess.CompletedProcess[str]:
    """Run the script over one case whose stub contradicts its recorded output."""
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    (test_dir / "bad.sv").write_text("module bad; endmodule\n")
    (test_dir / "bad.expected").write_text("expected output\n")
    return _run_sim_script(test_dir, stub_binary(exit_code=0, stdout="wrong output\n"))


def _run_over_a_directory_holding_no_pair(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> subprocess.CompletedProcess[str]:
    """Run the script over a directory with no .sv/.expected pair in it."""
    test_dir = tmp_path / "tests"
    test_dir.mkdir()
    return _run_sim_script(test_dir, stub_binary(exit_code=0, stdout=""))


def test_exit_one_on_mismatch(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    """Script should exit 1 when a case's output differs from its recording."""
    assert _run_mismatching_case(tmp_path, stub_binary).returncode == 1


def test_diff_shown_on_mismatch(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    """Script should print the recorded text a mismatching case was judged by."""
    assert "expected" in _run_mismatching_case(tmp_path, stub_binary).stdout


def test_exit_one_when_no_pairs(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    """Script should exit 1 when the directory holds no test pair."""
    assert _run_over_a_directory_holding_no_pair(tmp_path, stub_binary).returncode == 1


def test_error_printed_when_no_pairs(
    tmp_path: Path, stub_binary: Callable[..., Path],
) -> None:
    """Script should report on standard error when the directory holds no pair."""
    assert "error" in _run_over_a_directory_holding_no_pair(
        tmp_path, stub_binary,
    ).stderr
