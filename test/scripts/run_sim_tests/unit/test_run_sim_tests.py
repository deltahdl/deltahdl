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
        assert {"hello", "fail"} <= set(names)

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

    def test_every_e2e_source_has_an_expected_file(self, rst: ModuleType) -> None:
        """Every source in the real e2e directory should be a case.

        collect_tests skips a .sv with no .expected beside it, which is what
        lets a shared file sit in the directory without being run as a case.
        The skip is silent, so a source meant as a case and left unpaired
        asserts nothing and reads as covered. This is the claim that keeps the
        directory holding nothing the skip could hide, and it is over TEST_DIR
        itself rather than a fixture because the directory is its subject.
        """
        unpaired = [
            sv.name for sv in sorted(rst.TEST_DIR.glob("*.sv"))
            if not sv.with_suffix(".expected").exists()
        ]
        assert not unpaired


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
        """run_test() should return False when stdout differs from expected."""
        ok, _ = _run_over_streams(
            rst, tmp_path, "wrong output\n", "", "expected output\n",
        )
        assert not ok

    def test_the_detail_holds_both_sides_of_a_mismatch(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test()'s detail should quote the recorded text and the run's."""
        detail = _run_over_streams(
            rst, tmp_path, "wrong output\n", "", "expected output\n",
        )[1]
        missing = [t for t in ("expected output", "wrong output")
                   if t not in detail]
        assert not missing

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
        assert not _run_over_case(rst, tmp_path, "silent", 0)[1][0]

    def test_a_differing_status_is_named_in_the_detail(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should name the status it wanted and the one it got."""
        (tmp_path / "silent.exit").write_text("1\n")
        detail = _run_over_case(rst, tmp_path, "silent", 0)[1][1]
        assert "expected exit status 1, got 0" in detail

    def test_a_case_without_an_exit_file_judges_the_text_alone(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should pass a matching text whatever the status was."""
        _, outcome = _run_over_case(rst, tmp_path, "loose", 3)
        assert outcome == (True, "")

    def test_a_malformed_exit_file_fails_the_case_rather_than_raising(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should fail a case whose .exit file holds no status."""
        (tmp_path / "bogus.exit").write_text("yes\n")
        assert not _run_over_case(rst, tmp_path, "bogus", 0)[1][0]

    def test_a_malformed_exit_file_is_named_in_the_detail(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should name the .exit file and the text it holds."""
        status_path = tmp_path / "unreadable.exit"
        status_path.write_text("yes\n")
        detail = _run_over_case(rst, tmp_path, "unreadable", 4)[1][1]
        missing = [t for t in (str(status_path), "'yes'") if t not in detail]
        assert not missing

    def test_a_negative_status_is_accepted(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should read a signed status from a .exit file."""
        (tmp_path / "killed.exit").write_text("-1\n")
        assert _run_over_case(rst, tmp_path, "killed", -1)[1] == (True, "")


def _run_over_two_invocations(
    rst: ModuleType, tmp_path: Path, before_text: str, before_code: int | None,
) -> tuple[list[tuple[list[str], str]], tuple[bool, str]]:
    """Run run_test() over a case whose .before file holds before_text.

    The .sv, .args and .expected files are written for the caller. The .args
    file names one argument, so a test can tell the two invocations apart by
    their command lines, and the .expected file holds what the stub prints for
    the invocation under test alone. before_code is the status the earlier
    invocation exits with, and None makes it time out instead. Every invocation
    the stub saw comes back as its command line and the directory it ran in, in
    the order the invocations were made, so a test about the order or about the
    directory can read them.
    """
    sv = tmp_path / "two.sv"
    sv.write_text("module two; endmodule\n")
    (tmp_path / "two.before").write_text(before_text)
    (tmp_path / "two.args").write_text("--under-test\n")
    expected_path = tmp_path / "two.expected"
    expected_path.write_text("bound\n")

    calls: list[tuple[list[str], str]] = []

    def fake_run(cmd: list[str], **kwargs: object) -> MagicMock:
        calls.append((cmd, str(kwargs["cwd"])))
        first = len(calls) == 1
        if first and before_code is None:
            raise subprocess.TimeoutExpired(cmd="deltahdl", timeout=30)
        stub = MagicMock()
        stub.returncode = before_code if first else 0
        stub.stdout = "compiled\n" if first else "bound\n"
        stub.stderr = ""
        return stub

    with patch.object(rst.subprocess, "run", side_effect=fake_run):
        outcome: tuple[bool, str] = rst.run_test(sv, expected_path)
    return calls, outcome


class TestBeforeArguments:
    """Tests for the invocation a case names in its .before file."""

    def test_runs_the_named_invocation_before_the_one_under_test(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should run the .before command line first."""
        calls, _ = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 0,
        )
        source = str(tmp_path / "two.sv")
        assert [cmd for cmd, _ in calls] == [
            [str(rst.BINARY), source, "--precompile-into", "cells"],
            [str(rst.BINARY), source, "--under-test"],
        ]

    def test_a_blank_line_names_no_earlier_argument(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should pass no empty argument for a blank .before line."""
        calls, _ = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\n\ncells\n", 0,
        )
        assert calls[0][0][2:] == ["--precompile-into", "cells"]

    def test_both_invocations_run_in_one_directory(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should run both invocations in one directory it made.

        A precompiled library the earlier invocation writes under a relative
        path lands in the directory that invocation ran in, and the bind after
        it reads the library back from the directory it runs in, so the two
        directories being one is what lets a case name that file once.
        """
        calls, _ = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 0,
        )
        directories = [work_dir for _, work_dir in calls]
        assert directories[0] == directories[1]

    def test_the_invocations_run_outside_the_repository(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should run an invocation outside the repository.

        A precompiled library is written under the directory an invocation
        runs in, so running inside the repository would leave the library in
        test/src/e2e/ for `git status` to report.
        """
        calls, _ = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 0,
        )
        work_dir = calls[0][1]
        assert rst.REPO_ROOT not in Path(work_dir).parents

    def test_only_the_invocation_under_test_is_compared_to_expected(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should judge the case on the last invocation's output.

        The stub prints 'compiled' for the earlier invocation and 'bound' for
        the one under test, and the .expected file holds 'bound' alone.
        """
        _, outcome = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 0,
        )
        assert outcome == (True, "")

    def test_a_failing_earlier_invocation_fails_the_case(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should fail a case whose earlier invocation exited 1."""
        _, (ok, _) = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 1,
        )
        assert not ok

    def test_a_failing_earlier_invocation_is_named_in_the_detail(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should name the .before file and the status it exited."""
        detail = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 1,
        )[1][1]
        assert "two.before: exited 1" in detail

    def test_the_invocation_under_test_does_not_run_after_a_failure(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should not run the second invocation after the first."""
        calls, _ = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", 1,
        )
        assert len(calls) == 1

    def test_an_earlier_invocation_that_times_out_fails_the_case(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """run_test() should fail the case rather than raise on a timeout."""
        outcome = _run_over_two_invocations(
            rst, tmp_path, "--precompile-into\ncells\n", None,
        )[1]
        assert outcome == (False, "two.before: TIMEOUT")
