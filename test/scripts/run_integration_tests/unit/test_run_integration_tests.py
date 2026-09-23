import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import patch

RunCase = Callable[[str, int, str, str], tuple[list[str], tuple[bool, str]]]

_HOLDS = ":assert: (1 == 1)\n"
_SIMULATION = ":subclause: 8.25\n:stage: simulation\n"
_ELABORATION = ":subclause: 8.25\n:stage: elaboration\n"
_PARSING = ":subclause: 8.25\n:stage: parsing\n"
_REJECTED = _ELABORATION + ":should_fail_because: the rule under test forbids it\n"


def test_collects_the_sv_files_in_name_order(
    rit: ModuleType, tmp_path: Path,
) -> None:
    (tmp_path / "beta.sv").write_text("module beta; endmodule\n")
    (tmp_path / "alpha.sv").write_text("module alpha; endmodule\n")
    with patch.object(rit, "TEST_DIR", tmp_path):
        assert [p.name for p in rit.collect_tests()] == ["alpha.sv", "beta.sv"]


def test_collects_no_file_that_is_not_sv(rit: ModuleType, tmp_path: Path) -> None:
    (tmp_path / "notes.txt").write_text("not a test\n")
    with patch.object(rit, "TEST_DIR", tmp_path):
        assert not rit.collect_tests()


def test_a_case_without_a_subclause_fails_naming_the_header(
    run_case: RunCase,
) -> None:
    _, (_, detail) = run_case(":stage: simulation\n", 0, _HOLDS, "")
    assert ":subclause:" in detail


def test_a_subclause_that_is_not_a_number_fails_the_case(run_case: RunCase) -> None:
    _, (ok, _) = run_case(":subclause: classes\n:stage: simulation\n", 0, _HOLDS, "")
    assert not ok


def test_a_case_without_a_stage_fails_naming_the_header(run_case: RunCase) -> None:
    _, (_, detail) = run_case(":subclause: 8.25\n", 0, _HOLDS, "")
    assert ":stage:" in detail


def test_an_unknown_stage_fails_the_case(run_case: RunCase) -> None:
    _, (ok, _) = run_case(":subclause: 8.25\n:stage: preprocessing\n", 0, "", "")
    assert not ok


def test_a_malformed_header_runs_nothing(run_case: RunCase) -> None:
    seen, _ = run_case(":subclause: 8.25\n", 0, "", "")
    assert not seen


def test_the_command_starts_with_the_binary(
    rit: ModuleType, run_case: RunCase,
) -> None:
    seen, _ = run_case(_SIMULATION, 0, _HOLDS, "")
    assert seen[0] == str(rit.BINARY)


def test_the_command_ends_with_the_file(run_case: RunCase) -> None:
    seen, _ = run_case(_SIMULATION, 0, _HOLDS, "")
    assert Path(seen[-1]).name == "case.sv"


def test_a_simulation_passes_no_option(run_case: RunCase) -> None:
    seen, _ = run_case(_SIMULATION, 0, _HOLDS, "")
    assert not seen[1:-1]


def test_an_elaboration_passes_lint_only(run_case: RunCase) -> None:
    seen, _ = run_case(_ELABORATION, 0, "", "")
    assert seen[1:-1] == ["--lint-only"]


def test_a_parse_passes_parse_only(run_case: RunCase) -> None:
    seen, _ = run_case(_PARSING, 0, "", "")
    assert seen[1:-1] == ["--parse-only"]


def test_an_accepted_elaboration_passes(run_case: RunCase) -> None:
    assert run_case(_ELABORATION, 0, "", "")[1] == (True, "")


def test_a_nonzero_exit_fails_an_accepting_case_with_the_status(
    run_case: RunCase,
) -> None:
    outcome = run_case(_ELABORATION, 1, "", "error: no\n")[1]
    assert outcome == (False, "exited 1\nerror: no\n")


def test_a_simulation_printing_no_assert_line_fails(run_case: RunCase) -> None:
    assert not run_case(_SIMULATION, 0, "ran\n", "")[1][0]


def test_a_simulation_whose_assert_lines_hold_passes(run_case: RunCase) -> None:
    outcome = run_case(_SIMULATION, 0, _HOLDS + ":assert: (0 == 0)\n", "")[1]
    assert outcome == (True, "")


def test_a_simulation_with_a_false_assert_line_fails_naming_it(
    run_case: RunCase,
) -> None:
    outcome = run_case(_SIMULATION, 0, _HOLDS + ":assert: (0 == 5)\n", "")[1]
    assert outcome == (False, "Assertion failed: (0 == 5)")


def test_a_rejection_citing_a_clause_under_the_subclause_passes(
    run_case: RunCase,
) -> None:
    assert run_case(_REJECTED, 1, "", "error: no (§8.25.1)\n")[1] == (True, "")


def test_a_rejection_citing_the_subclause_itself_passes(run_case: RunCase) -> None:
    assert run_case(_REJECTED, 1, "", "error: no (§8.25)\n")[1] == (True, "")


def test_a_rejection_citing_only_an_enclosing_clause_fails(
    run_case: RunCase,
) -> None:
    assert not run_case(_REJECTED, 1, "", "error: no (§8)\n")[1][0]


def test_a_rejection_citing_a_sibling_sharing_digits_fails(
    run_case: RunCase,
) -> None:
    assert not run_case(_REJECTED, 1, "", "error: no (§8.251)\n")[1][0]


def test_a_rejection_citing_no_clause_fails_naming_the_subclause(
    run_case: RunCase,
) -> None:
    outcome = run_case(_REJECTED, 1, "", "error: no\n")[1]
    assert outcome == (False, "expected a rejection under §8.25, got:\nerror: no\n")


def test_an_accepted_case_that_should_fail_fails(run_case: RunCase) -> None:
    assert not run_case(_REJECTED, 0, "", "")[1][0]


def test_a_crash_is_no_rejection(run_case: RunCase) -> None:
    outcome = run_case(_REJECTED, 134, "", "error: no (§8.25)\n")[1]
    assert outcome == (
        False,
        "expected deltahdl to reject the code, it exited 134\nerror: no (§8.25)\n",
    )


def test_a_timeout_fails_the_case(rit: ModuleType, tmp_path: Path) -> None:
    sv = tmp_path / "slow.sv"
    sv.write_text(f"/*\n{_ELABORATION}*/\nmodule slow; endmodule\n")
    with patch.object(
        rit.subprocess, "run",
        side_effect=subprocess.TimeoutExpired(cmd="deltahdl", timeout=30),
    ):
        assert rit.run_test(sv) == (False, "TIMEOUT")


def test_running_the_package_as_a_module_calls_main(
    rit: ModuleType,
    calls_made_by_running_as_a_module: Callable[[ModuleType], list[str]],
) -> None:
    assert calls_made_by_running_as_a_module(rit) == ["main"]
