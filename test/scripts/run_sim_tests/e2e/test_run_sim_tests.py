"""End-to-end tests for run_sim_tests module."""

import subprocess
import sys
import textwrap
from pathlib import Path

import test_common

SCRIPTS_DIR = test_common.REPO_ROOT / "scripts"


def _run_sim_script(test_dir, binary_path):
    """Run run_sim_tests.main() in a subprocess with patched paths.

    Args:
        test_dir: Path to the directory containing .sv/.expected pairs.
        binary_path: Path to the stub binary to use.

    Returns:
        subprocess.CompletedProcess with stdout, stderr, and returncode.
    """
    code = textwrap.dedent(f"""\
        import sys
        sys.path.insert(0, {str(SCRIPTS_DIR)!r})
        from pathlib import Path
        import run_sim_tests
        import test_common
        run_sim_tests.TEST_DIR = Path({str(test_dir)!r})
        test_common.BINARY = Path({str(binary_path)!r})
        run_sim_tests.BINARY = test_common.BINARY
        run_sim_tests.main()
    """)
    return subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )


class TestAllPassing:
    """E2E test: all tests pass -> exit 0."""

    def test_exit_zero_when_all_pass(self, tmp_path, stub_binary):
        """Script should exit 0 when stub binary echoes expected output."""
        test_dir = tmp_path / "tests"
        test_dir.mkdir()
        (test_dir / "hello.sv").write_text("module hello; endmodule\n")
        (test_dir / "hello.expected").write_text("Hello, World!\n")

        binary = stub_binary(exit_code=0, stdout="Hello, World!\n")
        result = _run_sim_script(test_dir, binary)

        assert result.returncode == 0, (
            f"Expected exit 0, got {result.returncode}\n"
            f"stdout: {result.stdout}\nstderr: {result.stderr}"
        )


class TestFailingTest:
    """E2E test: mismatched output -> exit 1 with diff."""

    def test_exit_one_with_diff_on_mismatch(self, tmp_path, stub_binary):
        """Script should exit 1 and show diff when output mismatches."""
        test_dir = tmp_path / "tests"
        test_dir.mkdir()
        (test_dir / "bad.sv").write_text("module bad; endmodule\n")
        (test_dir / "bad.expected").write_text("expected output\n")

        binary = stub_binary(exit_code=0, stdout="wrong output\n")
        result = _run_sim_script(test_dir, binary)

        assert result.returncode == 1
        assert "expected output" in result.stdout or "expected" in result.stdout


class TestNoTestPairs:
    """E2E test: no .sv/.expected pairs -> exit 1 with error."""

    def test_exit_one_with_error_when_no_pairs(self, tmp_path, stub_binary):
        """Script should exit 1 and print error when no test pairs exist."""
        test_dir = tmp_path / "tests"
        test_dir.mkdir()
        # No .sv/.expected pairs at all.

        binary = stub_binary(exit_code=0, stdout="")
        result = _run_sim_script(test_dir, binary)

        assert result.returncode == 1
        assert "error" in result.stderr
