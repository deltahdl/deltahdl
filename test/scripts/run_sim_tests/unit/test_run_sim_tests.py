import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch


def _run_over_streams(
    rst: ModuleType, tmp_path: Path, out: str, err: str, expected: str,
) -> tuple[bool, str]:
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


def test_finds_sv_expected_pairs(rst: ModuleType, sim_test_tree: Path) -> None:
    with patch.object(rst, "TEST_DIR", sim_test_tree):
        pairs = rst.collect_tests()
    names = [sv.stem for sv, _ in pairs]
    assert {"hello", "fail"} <= set(names)


def test_ignores_sv_without_expected(rst: ModuleType, sim_test_tree: Path) -> None:
    with patch.object(rst, "TEST_DIR", sim_test_tree):
        pairs = rst.collect_tests()
    names = [sv.stem for sv, _ in pairs]
    assert "orphan" not in names


def test_returns_empty_list_when_no_pairs(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "readme.txt").write_text("nothing here\n")
    with patch.object(rst, "TEST_DIR", tmp_path):
        pairs = rst.collect_tests()
    assert not pairs


def test_every_e2e_source_has_an_expected_file(rst: ModuleType) -> None:
    unpaired = [
        sv.name for sv in sorted(rst.TEST_DIR.glob("*.sv"))
        if not sv.with_suffix(".expected").exists()
    ]
    assert not unpaired


def test_returns_true_on_matching_output(rst: ModuleType, tmp_path: Path) -> None:
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


def test_returns_false_on_mismatched_output(rst: ModuleType, tmp_path: Path) -> None:
    ok, _ = _run_over_streams(
        rst, tmp_path, "wrong output\n", "", "expected output\n",
    )
    assert not ok


def test_the_detail_holds_both_sides_of_a_mismatch(rst: ModuleType, tmp_path: Path) -> None:
    detail = _run_over_streams(
        rst, tmp_path, "wrong output\n", "", "expected output\n",
    )[1]
    missing = [t for t in ("expected output", "wrong output")
               if t not in detail]
    assert not missing


def test_strips_trailing_newlines_before_comparing(rst: ModuleType, tmp_path: Path) -> None:
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


def test_returns_timeout_on_timeout_expired(rst: ModuleType, tmp_path: Path) -> None:
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
    rst: ModuleType, tmp_path: Path,
) -> None:
    result = _run_over_streams(
        rst, tmp_path, "", "error: syntax error\n", "error: syntax error\n",
    )
    assert result == (True, "")


def test_compares_standard_output_ahead_of_standard_error(rst: ModuleType, tmp_path: Path) -> None:
    result = _run_over_streams(
        rst, tmp_path, "displayed\n", "error: rejected\n",
        "displayed\nerror: rejected\n",
    )
    assert result == (True, "")


def test_matches_a_reported_path_named_relative_to_the_repository(
    rst: ModuleType, tmp_path: Path,
) -> None:
    named = rst.REPO_ROOT / "test" / "src" / "e2e" / "reject.sv"
    result = _run_over_streams(
        rst, tmp_path, "", f"{named}:3:1: error: rejected\n",
        "test/src/e2e/reject.sv:3:1: error: rejected\n",
    )
    assert result == (True, "")


def test_passes_the_named_arguments_after_the_source_path(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "opt.args").write_text("--lint-only\n--top\nm\n")
    cmd, _ = _run_over_case(rst, tmp_path, "opt", 0)
    assert cmd == [
        str(rst.BINARY), str(tmp_path / "opt.sv"),
        "--lint-only", "--top", "m",
    ]


def test_a_blank_line_names_no_argument(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "blank.args").write_text("--lint-only\n\n--synth\n")
    cmd, _ = _run_over_case(rst, tmp_path, "blank", 0)
    assert cmd[2:] == ["--lint-only", "--synth"]


def test_a_case_without_an_args_file_runs_the_source_path_alone(
    rst: ModuleType, tmp_path: Path,
) -> None:
    cmd, _ = _run_over_case(rst, tmp_path, "plain", 0)
    assert cmd == [str(rst.BINARY), str(tmp_path / "plain.sv")]


def test_a_matching_status_passes_the_case(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "refused.exit").write_text("2\n")
    _, outcome = _run_over_case(rst, tmp_path, "refused", 2)
    assert outcome == (True, "")


def test_a_differing_status_fails_the_case(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "silent.exit").write_text("1\n")
    assert not _run_over_case(rst, tmp_path, "silent", 0)[1][0]


def test_a_differing_status_is_named_in_the_detail(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "silent.exit").write_text("1\n")
    detail = _run_over_case(rst, tmp_path, "silent", 0)[1][1]
    assert "expected exit status 1, got 0" in detail


def test_a_case_without_an_exit_file_judges_the_text_alone(rst: ModuleType, tmp_path: Path) -> None:
    _, outcome = _run_over_case(rst, tmp_path, "loose", 3)
    assert outcome == (True, "")


def test_a_malformed_exit_file_fails_the_case_rather_than_raising(
    rst: ModuleType, tmp_path: Path,
) -> None:
    (tmp_path / "bogus.exit").write_text("yes\n")
    assert not _run_over_case(rst, tmp_path, "bogus", 0)[1][0]


def test_a_malformed_exit_file_is_named_in_the_detail(rst: ModuleType, tmp_path: Path) -> None:
    status_path = tmp_path / "unreadable.exit"
    status_path.write_text("yes\n")
    detail = _run_over_case(rst, tmp_path, "unreadable", 4)[1][1]
    missing = [t for t in (str(status_path), "'yes'") if t not in detail]
    assert not missing


def test_a_negative_status_is_accepted(rst: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "killed.exit").write_text("-1\n")
    assert _run_over_case(rst, tmp_path, "killed", -1)[1] == (True, "")


def _run_over_two_invocations(
    rst: ModuleType, tmp_path: Path, before_text: str, before_code: int | None,
) -> tuple[list[tuple[list[str], str]], tuple[bool, str]]:
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


def test_runs_the_named_invocation_before_the_one_under_test(
    rst: ModuleType, tmp_path: Path,
) -> None:
    calls, _ = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 0,
    )
    source = str(tmp_path / "two.sv")
    assert [cmd for cmd, _ in calls] == [
        [str(rst.BINARY), source, "--precompile-into", "cells"],
        [str(rst.BINARY), source, "--under-test"],
    ]


def test_a_blank_line_names_no_earlier_argument(rst: ModuleType, tmp_path: Path) -> None:
    calls, _ = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\n\ncells\n", 0,
    )
    assert calls[0][0][2:] == ["--precompile-into", "cells"]


def test_both_invocations_run_in_one_directory(rst: ModuleType, tmp_path: Path) -> None:
    calls, _ = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 0,
    )
    directories = [work_dir for _, work_dir in calls]
    assert directories[0] == directories[1]


def test_the_invocations_run_outside_the_repository(rst: ModuleType, tmp_path: Path) -> None:
    calls, _ = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 0,
    )
    work_dir = calls[0][1]
    assert rst.REPO_ROOT not in Path(work_dir).parents


def test_only_the_invocation_under_test_is_compared_to_expected(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 0,
    )
    assert outcome == (True, "")


def test_a_failing_earlier_invocation_fails_the_case(rst: ModuleType, tmp_path: Path) -> None:
    _, (ok, _) = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 1,
    )
    assert not ok


def test_a_failing_earlier_invocation_is_named_in_the_detail(
    rst: ModuleType, tmp_path: Path,
) -> None:
    detail = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 1,
    )[1][1]
    assert "two.before: exited 1" in detail


def test_the_invocation_under_test_does_not_run_after_a_failure(
    rst: ModuleType, tmp_path: Path,
) -> None:
    calls, _ = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", 1,
    )
    assert len(calls) == 1


def test_an_earlier_invocation_that_times_out_fails_the_case(
    rst: ModuleType, tmp_path: Path,
) -> None:
    outcome = _run_over_two_invocations(
        rst, tmp_path, "--precompile-into\ncells\n", None,
    )[1]
    assert outcome == (False, "two.before: TIMEOUT")


def _run_over_artifact(
    rst: ModuleType,
    tmp_path: Path,
    named: str,
    written: str | None,
    recorded: str | None,
) -> tuple[list[str], tuple[bool, str]]:
    sv = tmp_path / "artifact.sv"
    sv.write_text("module artifact; endmodule\n")
    (tmp_path / "artifact.artifact").write_text(named)
    if recorded is not None:
        (tmp_path / "artifact.artifact.expected").write_text(recorded)
    expected_path = tmp_path / "artifact.expected"
    expected_path.write_text("ran\n")

    directories: list[str] = []

    def fake_run(cmd: list[str], **kwargs: object) -> MagicMock:
        del cmd
        work_dir = str(kwargs["cwd"])
        directories.append(work_dir)
        if written is not None:
            (Path(work_dir) / named.strip()).write_text(written)
        stub = MagicMock()
        stub.stdout = "ran\n"
        stub.stderr = ""
        stub.returncode = 0
        return stub

    with patch.object(rst.subprocess, "run", side_effect=fake_run):
        outcome: tuple[bool, str] = rst.run_test(sv, expected_path)
    return directories, outcome


_VCD_HEADER = (
    "$date\n  {}\n$end\n"
    "$version\n  DeltaHDL 0.1.0\n$end\n"
    "$timescale 1ns $end\n"
    "$enddefinitions $end\n"
)


def test_a_matching_artifact_passes_the_case(rst: ModuleType, tmp_path: Path) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", "same\n", "same\n",
    )
    assert outcome == (True, "")


def test_a_differing_artifact_fails_the_case(rst: ModuleType, tmp_path: Path) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", "written\n", "recorded\n",
    )
    assert outcome[0] is False


def test_a_differing_artifact_is_named_in_the_detail(rst: ModuleType, tmp_path: Path) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", "written\n", "recorded\n",
    )
    assert outcome[1] == "dump.vcd expected:\nrecorded\ngot:\nwritten\n"


def test_a_date_section_may_differ_without_failing_the_case(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_artifact(
        rst,
        tmp_path,
        "dump.vcd\n",
        _VCD_HEADER.format("June 25, 1989 09:24:35"),
        _VCD_HEADER.format("May 2, 2026 11:00:00"),
    )
    assert outcome == (True, "")


def test_a_difference_past_the_date_section_still_fails_the_case(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_artifact(
        rst,
        tmp_path,
        "dump.vcd\n",
        _VCD_HEADER.format("June 25, 1989 09:24:35")
        + "$var wire 1 ! clk $end\n",
        _VCD_HEADER.format("May 2, 2026 11:00:00"),
    )
    assert outcome[0] is False


def test_a_file_the_run_did_not_write_fails_the_case(rst: ModuleType, tmp_path: Path) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", None, "recorded\n",
    )
    assert outcome[0] is False


def test_a_file_the_run_did_not_write_is_named_in_the_detail(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", None, "recorded\n",
    )
    assert outcome[1] == "dump.vcd: the run wrote no such file"


def test_an_artifact_without_a_recorded_copy_fails_the_case(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", "written\n", None,
    )
    assert outcome[0] is False


def test_an_artifact_without_a_recorded_copy_is_named_in_the_detail(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", "written\n", None,
    )
    assert outcome[1] == (
        "artifact.artifact.expected: no recorded contents for dump.vcd"
    )


def test_an_artifact_file_naming_no_file_fails_the_case(rst: ModuleType, tmp_path: Path) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "\n", None, "recorded\n",
    )
    assert outcome[0] is False


def test_an_artifact_file_naming_two_files_is_named_in_the_detail(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_artifact(
        rst, tmp_path, "one.vcd\ntwo.vcd\n", None, "recorded\n",
    )
    assert outcome[1].endswith(
        "artifact.artifact: expected one file name, got 2",
    )


def test_the_run_writes_its_artifact_outside_the_repository(
    rst: ModuleType, tmp_path: Path,
) -> None:
    directories, _ = _run_over_artifact(
        rst, tmp_path, "dump.vcd\n", "same\n", "same\n",
    )
    assert rst.REPO_ROOT not in Path(directories[0]).parents


def test_a_case_without_an_artifact_file_judges_the_text_alone(
    rst: ModuleType, tmp_path: Path,
) -> None:
    _, outcome = _run_over_case(rst, tmp_path, "plain", 0)
    assert outcome == (True, "")


def test_running_the_package_as_a_module_calls_main(
    rst: ModuleType,
    calls_made_by_running_as_a_module: Callable[[ModuleType], list[str]],
) -> None:
    assert calls_made_by_running_as_a_module(rst) == ["main"]
