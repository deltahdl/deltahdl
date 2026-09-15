import ast
import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

CaptureRunCmd = Callable[[ModuleType, Callable[[], Any]], list[str]]


def _d_flag_values(cmd: list[str]) -> list[str]:
    return [
        cmd[i + 1] for i, v in enumerate(cmd) if v == "-D" and i + 1 < len(cmd)
    ]


def _simulate_over_a_failing_assertion(rst: ModuleType) -> tuple[bool, str, int]:
    mock_result = MagicMock(
        returncode=0, stdout=":assert: (1 == 2)\n", stderr=""
    )
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        outcome: tuple[bool, str, int] = rst.run_test(
            "/fake/test.sv", simulate=True,
        )
    return outcome


def test_returns_naturally_sorted_paths(rst: ModuleType) -> None:
    fake_paths = [
        "/x/chapter-25/3-interface.sv",
        "/x/chapter-5/10-arrays.sv",
        "/x/chapter-5/3-types.sv",
        "/x/chapter-26/1-pkg.sv",
    ]
    with patch.object(rst.glob, "glob", return_value=fake_paths):
        result = rst.collect_tests()
    assert result == [
        "/x/chapter-5/3-types.sv",
        "/x/chapter-5/10-arrays.sv",
        "/x/chapter-25/3-interface.sv",
        "/x/chapter-26/1-pkg.sv",
    ]


def test_returns_empty_when_no_files(rst: ModuleType) -> None:
    with patch.object(rst.glob, "glob", return_value=[]):
        result = rst.collect_tests()
    assert result == []


def test_returns_true_on_exit_zero(rst: ModuleType) -> None:
    mock_result = MagicMock(returncode=0, stderr="")
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        actual = rst.run_test("/fake/test.sv")
    assert actual == (True, "", 0)


def test_returns_false_on_nonzero_exit(rst: ModuleType) -> None:
    mock_result = MagicMock(returncode=1, stderr="parse error\n")
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        actual = rst.run_test("/fake/test.sv")
    assert actual == (False, "parse error\n", 1)


def test_reports_the_code_a_signal_death_leaves(rst: ModuleType) -> None:
    mock_result = MagicMock(returncode=-11, stderr="")
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        actual = rst.run_test("/fake/test.sv")
    assert actual == (False, "", -11)


def test_timeout_propagates(rst: ModuleType) -> None:
    raised = False
    with patch.object(
        rst.subprocess, "run",
        side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
    ):
        try:
            rst.run_test("/fake/test.sv")
        except subprocess.TimeoutExpired:
            raised = True
    assert raised


def test_simulate_pass_with_assertions(rst: ModuleType) -> None:
    mock_result = MagicMock(returncode=0, stdout=":assert: (True)\n", stderr="")
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        actual = rst.run_test("/fake/test.sv", simulate=True)
    assert actual == (True, "", 0)


def test_simulate_fail_on_assertion(rst: ModuleType) -> None:
    ok, _, _ = _simulate_over_a_failing_assertion(rst)
    assert ok is False


def test_simulate_names_the_failed_assertion(rst: ModuleType) -> None:
    _, detail, _ = _simulate_over_a_failing_assertion(rst)
    assert "Assertion failed" in detail


def test_simulate_fail_on_nonzero_exit(rst: ModuleType) -> None:
    mock_result = MagicMock(returncode=1, stdout="", stderr="error\n")
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        actual = rst.run_test("/fake/test.sv", simulate=True)
    assert actual == (False, "error\n", 1)


def test_defines_passed_as_dash_d_flags(rst: ModuleType, capture_run_cmd: CaptureRunCmd) -> None:
    cmd = capture_run_cmd(
        rst, lambda: rst.run_test("/fake/test.sv", defines=["FOO", "BAR=2"]),
    )
    assert _d_flag_values(cmd) == ["FOO", "BAR=2"]


def test_extracts_all_fields(rst: ModuleType, tmp_path: Path) -> None:
    sv = tmp_path / "test.sv"
    sv.write_text(
        "/*\n:name: foo\n:type: simulation elaboration parsing\n"
        ":tags: 7.3.2\n:should_fail_because: bad code\n*/\n"
        "module top; endmodule\n"
    )
    assert rst.parse_metadata(str(sv)) == {
        "name": "foo",
        "type": "simulation elaboration parsing",
        "tags": "7.3.2",
        "should_fail_because": "bad code",
    }


def test_returns_empty_dict_when_no_comment(rst: ModuleType, tmp_path: Path) -> None:
    sv = tmp_path / "bare.sv"
    sv.write_text("module bare; endmodule\n")
    assert not rst.parse_metadata(str(sv))


def test_returns_empty_type_when_absent(rst: ModuleType, tmp_path: Path) -> None:
    sv = tmp_path / "no_type.sv"
    sv.write_text("/*\n:name: no_type\n:tags: 5.10\n*/\nmodule m; endmodule\n")
    assert set(rst.parse_metadata(str(sv))) == {"name", "tags"}


def test_constant_true(rst: ModuleType) -> None:
    assert rst.eval_node(ast.Constant(value=True)) is True


def test_constant_integer(rst: ModuleType) -> None:
    assert rst.eval_node(ast.Constant(value=42)) == 42


def test_equality_pass(rst: ModuleType) -> None:
    tree = ast.parse("('hello' == 'hello')", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_equality_fail(rst: ModuleType) -> None:
    tree = ast.parse("(1 == 2)", mode="eval")
    assert rst.eval_node(tree.body) is False


def test_in_operator(rst: ModuleType) -> None:
    tree = ast.parse("('est' in 'Test')", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_not_in_operator(rst: ModuleType) -> None:
    tree = ast.parse("('xyz' not in 'Test')", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_bool_and(rst: ModuleType) -> None:
    tree = ast.parse("(True and True)", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_bool_or(rst: ModuleType) -> None:
    tree = ast.parse("(False or True)", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_unary_not(rst: ModuleType) -> None:
    tree = ast.parse("(not False)", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_unsupported_node_raises(rst: ModuleType) -> None:
    raised = False
    try:
        rst.eval_node(ast.Name(id="x"))
    except ValueError:
        raised = True
    assert raised


def _check_without_ast(rst: ModuleType, line: str) -> tuple[bool, str]:
    with patch("ast.parse", side_effect=SyntaxError):
        outcome: tuple[bool, str] = rst.check_assertions(line)
    return outcome


def test_passing_assertion(rst: ModuleType) -> None:
    assert rst.check_assertions(":assert: (True)") == (True, "")


def test_failing_assertion(rst: ModuleType) -> None:
    assert rst.check_assertions(":assert: (1 == 2)")[0] is False


def test_failing_assertion_names_the_failure(rst: ModuleType) -> None:
    assert "Assertion failed" in rst.check_assertions(":assert: (1 == 2)")[1]


def test_no_assertions_passes(rst: ModuleType) -> None:
    assert rst.check_assertions("hello world\n") == (True, "")


def test_multiple_assertions_all_pass(rst: ModuleType) -> None:
    stdout = ":assert: (True)\n:assert: (1 == 1)\n"
    assert rst.check_assertions(stdout) == (True, "")


def test_multiple_assertions_one_fails(rst: ModuleType) -> None:
    stdout = ":assert: (True)\n:assert: (1 == 2)\n"
    ok, _ = rst.check_assertions(stdout)
    assert ok is False


def test_syntax_error_fails(rst: ModuleType) -> None:
    assert rst.check_assertions(":assert: (!!!)")[0] is False


def test_syntax_error_names_the_parse_failure(rst: ModuleType) -> None:
    assert "Assertion parse error" in rst.check_assertions(":assert: (!!!)")[1]


def test_string_equality_pass(rst: ModuleType) -> None:
    assert rst.try_string_equality("('hello' == 'hello')") is True


def test_string_equality_fail(rst: ModuleType) -> None:
    assert rst.try_string_equality("('hello' == 'world')") is False


def test_string_equality_fallback_pass(rst: ModuleType) -> None:
    assert _check_without_ast(rst, ":assert: ('same' == 'same')") == (True, "")


def test_string_equality_fallback_fail(rst: ModuleType) -> None:
    assert _check_without_ast(rst, ":assert: ('abc' == 'xyz')")[0] is False


def test_string_equality_fallback_names_the_failure(rst: ModuleType) -> None:
    detail = _check_without_ast(rst, ":assert: ('abc' == 'xyz')")[1]
    assert "Assertion failed" in detail


def _score_expected_rejection(
    rst: ModuleType, tmp_path: Path, returncode: int, stderr: str,
    tags: str = "5.10",
) -> tuple[dict[str, Any], int]:
    sv = tmp_path / "chapter-5" / "xfail.sv"
    sv.parent.mkdir(parents=True)
    tag_line = f":tags: {tags}\n" if tags else ""
    sv.write_text(
        f"/*\n:name: xfail\n{tag_line}"
        ":should_fail_because: bad code\n*/\nmodule m; endmodule\n"
    )
    mock_result = MagicMock(returncode=returncode, stderr=stderr)
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        scored: tuple[dict[str, Any], int] = rst.build_result(str(sv))
        return scored


def _build_result_over_a_simulation_file(
    rst: ModuleType, tmp_path: Path,
) -> tuple[dict[str, Any], int, list[str]]:
    sv = tmp_path / "chapter-7" / "sim.sv"
    sv.parent.mkdir(parents=True)
    sv.write_text(
        "/*\n:name: sim\n:type: simulation elaboration parsing\n"
        ":tags: 7.3.2\n*/\nmodule m; endmodule\n"
    )
    mock_result = MagicMock(
        returncode=0, stdout=":assert: (True)\n", stderr=""
    )
    with patch.object(
        rst.subprocess, "run", return_value=mock_result,
    ) as mock_run:
        result, ok = rst.build_result(str(sv))
    cmd: list[str] = mock_run.call_args[0][0]
    return result, ok, cmd


class TestBuildResult:
    def test_pass_returns_correct_dict(self, rst: ModuleType, tmp_path: Path) -> None:
        sv = tmp_path / "chapter-5" / "foo.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: foo\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, ok = rst.build_result(str(sv))
        verdict = (ok, result["name"], result["chapter"], result["status"])
        assert verdict == (1, "5.10--foo.sv", "chapter-5", "pass")

    def test_fail_returns_correct_dict(self, rst: ModuleType, tmp_path: Path) -> None:
        sv = tmp_path / "chapter-5" / "bar.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: bar\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=1, stderr="error\n")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, ok = rst.build_result(str(sv))
        assert (ok, result["status"]) == (0, "fail")

    def test_timeout_returns_timeout_status(self, rst: ModuleType, tmp_path: Path) -> None:
        sv = tmp_path / "chapter-5" / "slow.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: slow\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        with patch.object(
            rst.subprocess, "run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ):
            result, ok = rst.build_result(str(sv))
        assert (ok, result["status"]) == (0, "timeout")

    def test_clean_rejection_still_scores_a_pass_for_an_expected_rejection(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1, "xfail.sv:1:1: error: redeclaration of 'v'\n",
        )
        assert (ok, result["status"]) == (1, "pass")

    def test_signal_death_does_not_score_a_pass_for_an_expected_rejection(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        result, ok = _score_expected_rejection(rst, tmp_path, -11, "")
        assert (ok, result["status"]) == (0, "fail")

    def test_exit_one_with_no_diagnostic_does_not_score_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        result, ok = _score_expected_rejection(rst, tmp_path, 1, "")
        assert (ok, result["status"]) == (0, "fail")

    def test_acceptance_does_not_score_a_pass_for_an_expected_rejection(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        result, ok = _score_expected_rejection(rst, tmp_path, 0, "")
        assert (ok, result["status"]) == (0, "fail")

    def test_expected_rejection_carries_should_fail_into_the_result(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        sv = tmp_path / "chapter-6" / "redeclare.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: redeclare\n:tags: 6.5\n"
            ":should_fail_because: Variable redeclaration\n*/\n"
            "module top; reg v; wire v; endmodule\n"
        )
        mock_result = MagicMock(returncode=1, stderr="redeclaration of 'v'\n")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, _ = rst.build_result(str(sv))
        assert result["should_fail"] is True

    def test_defines_passed_to_command(
        self,
        rst: ModuleType,
        tmp_path: Path,
        capture_run_cmd: CaptureRunCmd,
    ) -> None:
        sv = tmp_path / "chapter-5" / "defs.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: defs\n:tags: 5.6.4\n"
            ":defines: TEST_VAR VAR_1=2\n*/\nmodule m; endmodule\n"
        )
        cmd = capture_run_cmd(rst, lambda: rst.build_result(str(sv)))
        assert _d_flag_values(cmd) == ["TEST_VAR", "VAR_1=2"]

    def test_simulation_mode_used_for_simulation_type(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        cmd = _build_result_over_a_simulation_file(rst, tmp_path)[2]
        assert "--lint-only" not in cmd

    def test_a_simulated_file_whose_assertions_hold_scores_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        result, ok, _ = _build_result_over_a_simulation_file(rst, tmp_path)
        assert (ok, result["status"]) == (1, "pass")

    def test_name_includes_clause_number_from_tags(self, rst: ModuleType, tmp_path: Path) -> None:
        sv = tmp_path / "chapter-7" / "arrays" / "unpacked" / "slice.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: slice\n:tags: 7.4.3\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=0, stderr="")
        with (
            patch.object(rst.subprocess, "run", return_value=mock_result),
            patch.object(rst, "TEST_DIR", tmp_path),
        ):
            result, _ = rst.build_result(str(sv))
        assert result["name"] == "7.4.3--arrays/unpacked/slice.sv"

    def test_name_skips_clause_when_already_present(self, rst: ModuleType, tmp_path: Path) -> None:
        sv = tmp_path / "chapter-5" / "5.6.4--compiler-directives-define.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: define\n:tags: 5.6.4\n*/\nmodule m; endmodule\n"
        )
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, _ = rst.build_result(str(sv))
        assert result["name"] == "5.6.4--compiler-directives-define.sv"

    def test_name_omits_clause_when_no_tags(self, rst: ModuleType, tmp_path: Path) -> None:
        sv = tmp_path / "chapter-5" / "bare.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: bare\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, _ = rst.build_result(str(sv))
        assert result["name"] == "bare.sv"

    def _build_result_with_oserror(
        self, rst: ModuleType, tmp_path: Path,
    ) -> tuple[dict[str, Any], int]:
        sv = tmp_path / "chapter-5" / "bad.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: bad\n*/\nmodule m; endmodule\n")
        with patch.object(
            rst, "parse_metadata",
            side_effect=OSError("read error"),
        ):
            result: tuple[dict[str, Any], int] = rst.build_result(str(sv))
            return result

    def test_exception_returns_ok_zero(self, rst: ModuleType, tmp_path: Path) -> None:
        _, ok = self._build_result_with_oserror(rst, tmp_path)
        assert ok == 0

    def test_exception_returns_fail_status(self, rst: ModuleType, tmp_path: Path) -> None:
        result, _ = self._build_result_with_oserror(rst, tmp_path)
        assert result["status"] == "fail"

    def test_exception_captures_stderr(self, rst: ModuleType, tmp_path: Path) -> None:
        result, _ = self._build_result_with_oserror(rst, tmp_path)
        assert "OSError: read error" in result["stderr"]

    def test_exception_logs_to_stderr(
        self,
        rst: ModuleType,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        self._build_result_with_oserror(rst, tmp_path)
        assert "read error" in capsys.readouterr().err


def test_rejection_naming_the_tagged_clause_scores_a_pass(rst: ModuleType, tmp_path: Path) -> None:
    result, ok = _score_expected_rejection(
        rst, tmp_path, 1,
        "xfail.sv:1:1: error: enum has an x assignment (§6.19)\n",
        "6.19",
    )
    assert (ok, result["status"]) == (1, "pass")


def test_rejection_naming_a_different_clause_does_not_score_a_pass(
    rst: ModuleType, tmp_path: Path,
) -> None:
    result, ok = _score_expected_rejection(
        rst, tmp_path, 1,
        "xfail.sv:1:1: error: net type mismatch (§7.3)\n",
        "6.19",
    )
    assert (ok, result["status"]) == (0, "fail")


def test_rejection_naming_no_clause_scores_a_pass(rst: ModuleType, tmp_path: Path) -> None:
    result, ok = _score_expected_rejection(
        rst, tmp_path, 1,
        "xfail.sv:1:1: error: cannot open include file 'x.svh'\n",
        "6.19",
    )
    assert (ok, result["status"]) == (1, "pass")


def test_rejection_for_a_file_with_no_clause_tag_scores_a_pass(
    rst: ModuleType, tmp_path: Path,
) -> None:
    result, ok = _score_expected_rejection(
        rst, tmp_path, 1,
        "xfail.sv:1:1: error: net type mismatch (§7.3)\n",
        "",
    )
    assert (ok, result["status"]) == (1, "pass")


def test_subclause_of_the_tagged_clause_scores_a_pass(rst: ModuleType, tmp_path: Path) -> None:
    result, ok = _score_expected_rejection(
        rst, tmp_path, 1,
        "xfail.sv:1:1: error: bad randomize() call (§16.12.17)\n",
        "16.12",
    )
    assert (ok, result["status"]) == (1, "pass")


def test_the_tagged_clause_reaches_the_result(rst: ModuleType, tmp_path: Path) -> None:
    result, _ = _score_expected_rejection(
        rst, tmp_path, 1,
        "xfail.sv:1:1: error: enum has an x assignment (§6.19)\n",
        "6.19",
    )
    assert result["clause"] == "6.19"


def test_running_the_package_as_a_module_calls_main(
    rst: ModuleType,
    calls_made_by_running_as_a_module: Callable[[ModuleType], list[str]],
) -> None:
    assert calls_made_by_running_as_a_module(rst) == ["main"]
