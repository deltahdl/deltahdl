"""Unit tests for run_sim_tests module."""

import subprocess
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch


def _run_over_streams(
    rst: ModuleType, tmp_path: Path, out: str, err: str, expected: str,
) -> tuple[bool, str]:
    """Run run_test() over a stub deltahdl writing out and err to its streams.

    The .sv file is written for the caller and the .expected file is given the
    expected text, so a test says only what the two streams hold and what the
    recording of them says.
    """
    sv = tmp_path / "streams.sv"
    sv.write_text("module streams; endmodule\n")
    expected_path = tmp_path / "streams.expected"
    expected_path.write_text(expected)

    stub = MagicMock()
    stub.stdout = out
    stub.stderr = err
    with patch.object(rst.subprocess, "run", return_value=stub):
        outcome: tuple[bool, str] = rst.run_test(sv, expected_path)
    return outcome


def _run_over_case(
    rst: ModuleType, tmp_path: Path, stem: str, returncode: int,
) -> tuple[list[str], tuple[bool, str]]:
    """Run run_test() over a stub deltahdl and return its command and outcome.

    The .sv file and the .expected file are written for the caller and are made
    to agree, so a test says only which optional sibling files the case carries
    and what status the stub exits with. The command line comes back so that a
    test about .args can read what the stub was asked to run, and the outcome
    comes back so that a test about .exit can read what run_test decided.
    """
    sv = tmp_path / f"{stem}.sv"
    sv.write_text("module m; endmodule\n")
    expected_path = tmp_path / f"{stem}.expected"
    expected_path.write_text("ran\n")

    seen: list[str] = []

    def fake_run(cmd: list[str], **_: object) -> MagicMock:
        seen.extend(cmd)
        stub = MagicMock()
        stub.stdout = "ran\n"
        stub.stderr = ""
        stub.returncode = returncode
        return stub

    with patch.object(rst.subprocess, "run", side_effect=fake_run):
        outcome: tuple[bool, str] = rst.run_test(sv, expected_path)
    return seen, outcome


class TestCollectTests:
    """Tests for the collect_tests() function."""

    def test_finds_sv_expected_pairs(
        self, rst: ModuleType, sim_test_tree: Path,
    ) -> None:
        """collect_tests() should return pairs of .sv and .expected files."""
        with patch.object(rst, "TEST_DIR", sim_test_tree):
            pairs = rst.collect_tests()
        names = [sv.stem for sv, _ in pairs]
        assert "hello" in names and "fail" in names

    def test_ignores_sv_without_expected(
        self, rst: ModuleType, sim_test_tree: Path,
    ) -> None:
        """collect_tests() should skip .sv files that lack a .expected."""
        with patch.object(rst, "TEST_DIR", sim_test_tree):
            pairs = rst.collect_tests()
        names = [sv.stem for sv, _ in pairs]
        assert "orphan" not in names

    def test_returns_empty_list_when_no_pairs(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """collect_tests() should return [] when no .sv/.expected pairs exist."""
        (tmp_path / "readme.txt").write_text("nothing here\n")
        with patch.object(rst, "TEST_DIR", tmp_path):
            pairs = rst.collect_tests()
        assert not pairs


class TestRunTest:
    """Tests for the run_test() function."""

    def test_returns_true_on_matching_output(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should return (True, '') when stdout matches expected."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("Hello, World!\n")

        mock_result = MagicMock()
        mock_result.stdout = "Hello, World!\n"
        mock_result.stderr = ""
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result = rst.run_test(sv, expected)
        assert result == (True, "")

    def test_returns_false_on_mismatched_output(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should return (False, diff) when stdout differs."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("expected output\n")

        mock_result = MagicMock()
        mock_result.stdout = "wrong output\n"
        mock_result.stderr = ""
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            ok, detail = rst.run_test(sv, expected)
        assert not ok and "expected output" in detail and "wrong output" in detail

    def test_strips_trailing_newlines_before_comparing(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should strip trailing newlines from both sides."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("output\n\n\n")

        mock_result = MagicMock()
        mock_result.stdout = "output\n"
        mock_result.stderr = ""
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result = rst.run_test(sv, expected)
        assert result == (True, "")

    def test_returns_timeout_on_timeout_expired(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should return (False, 'TIMEOUT') on TimeoutExpired."""
        sv = tmp_path / "test.sv"
        sv.write_text("module test; endmodule\n")
        expected = tmp_path / "test.expected"
        expected.write_text("output\n")

        with patch.object(
            rst.subprocess, "run",
            side_effect=subprocess.TimeoutExpired(cmd="deltahdl", timeout=30),
        ):
            result = rst.run_test(sv, expected)
        assert result == (False, "TIMEOUT")

    def test_matches_a_diagnostic_written_only_to_standard_error(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should compare a report deltahdl wrote to standard error."""
        result = _run_over_streams(
            rst, tmp_path, "", "error: syntax error\n", "error: syntax error\n",
        )
        assert result == (True, "")

    def test_compares_standard_output_ahead_of_standard_error(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should compare both streams, standard output first."""
        result = _run_over_streams(
            rst, tmp_path, "displayed\n", "error: rejected\n",
            "displayed\nerror: rejected\n",
        )
        assert result == (True, "")

    def test_matches_a_reported_path_named_relative_to_the_repository(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should cut the repository root off a path a report names."""
        named = rst.REPO_ROOT / "test" / "src" / "e2e" / "reject.sv"
        result = _run_over_streams(
            rst, tmp_path, "", f"{named}:3:1: error: rejected\n",
            "test/src/e2e/reject.sv:3:1: error: rejected\n",
        )
        assert result == (True, "")


class TestCaseArguments:
    """Tests for the arguments a case names in its .args file."""

    def test_passes_the_named_arguments_after_the_source_path(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should pass a case's .args lines after its source path."""
        (tmp_path / "opt.args").write_text("--lint-only\n--top\nm\n")
        cmd, _ = _run_over_case(rst, tmp_path, "opt", 0)
        assert cmd == [
            str(rst.BINARY), str(tmp_path / "opt.sv"),
            "--lint-only", "--top", "m",
        ]

    def test_a_blank_line_names_no_argument(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should pass no empty argument for a blank .args line."""
        (tmp_path / "blank.args").write_text("--lint-only\n\n--synth\n")
        cmd, _ = _run_over_case(rst, tmp_path, "blank", 0)
        assert cmd[2:] == ["--lint-only", "--synth"]

    def test_a_case_without_an_args_file_runs_the_source_path_alone(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should build a two-element command with no .args file."""
        cmd, _ = _run_over_case(rst, tmp_path, "plain", 0)
        assert cmd == [str(rst.BINARY), str(tmp_path / "plain.sv")]


class TestExpectedStatus:
    """Tests for the exit status a case names in its .exit file."""

    def test_a_matching_status_passes_the_case(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should pass when the status matches the .exit file."""
        (tmp_path / "refused.exit").write_text("2\n")
        _, outcome = _run_over_case(rst, tmp_path, "refused", 2)
        assert outcome == (True, "")

    def test_a_differing_status_fails_the_case(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should fail when the status differs from the .exit file."""
        (tmp_path / "silent.exit").write_text("1\n")
        _, (ok, detail) = _run_over_case(rst, tmp_path, "silent", 0)
        assert not ok and "expected exit status 1, got 0" in detail

    def test_a_case_without_an_exit_file_judges_the_text_alone(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should pass a matching text whatever the status was."""
        _, outcome = _run_over_case(rst, tmp_path, "loose", 3)
        assert outcome == (True, "")
