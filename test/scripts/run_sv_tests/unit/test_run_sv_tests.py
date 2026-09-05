"""Unit tests for run_sv_tests module."""

import ast
import io
import re
import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest


def _capture_run_cmd(rst: ModuleType, call: Callable[[], Any]) -> list[str]:
    """Run *call* with rst.subprocess.run stubbed; return the command invoked."""
    mock_result = MagicMock(returncode=0, stderr="")
    with patch.object(rst.subprocess, "run", return_value=mock_result) as mock_run:
        call()
    cmd: list[str] = mock_run.call_args[0][0]
    return cmd


def _d_flag_values(cmd: list[str]) -> list[str]:
    """Return the value following each ``-D`` token in *cmd*."""
    return [
        cmd[i + 1] for i, v in enumerate(cmd) if v == "-D" and i + 1 < len(cmd)
    ]


def _simulate_over_a_failing_assertion(
    rst: ModuleType,
) -> tuple[bool, str, int]:
    """Run run_test(simulate=True) over a run whose printed assertion is false."""
    mock_result = MagicMock(
        returncode=0, stdout=":assert: (1 == 2)\n", stderr=""
    )
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        outcome: tuple[bool, str, int] = rst.run_test(
            "/fake/test.sv", simulate=True,
        )
    return outcome


class TestCollectTests:
    """Tests for the collect_tests() function."""

    def test_returns_naturally_sorted_paths(self, rst: ModuleType) -> None:
        """collect_tests() should use natural sort: chapter-5 before chapter-25."""
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

    def test_returns_empty_when_no_files(self, rst: ModuleType) -> None:
        """collect_tests() should return an empty list when nothing matches."""
        with patch.object(rst.glob, "glob", return_value=[]):
            result = rst.collect_tests()
        assert result == []


class TestRunTest:
    """Tests for the run_test() function."""

    def test_returns_true_on_exit_zero(self, rst: ModuleType) -> None:
        """run_test() should return (True, '', 0) when subprocess exits 0."""
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            actual = rst.run_test("/fake/test.sv")
        assert actual == (True, "", 0)

    def test_returns_false_on_nonzero_exit(self, rst: ModuleType) -> None:
        """run_test() should return (False, stderr, code) on non-zero exit."""
        mock_result = MagicMock(returncode=1, stderr="parse error\n")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            actual = rst.run_test("/fake/test.sv")
        assert actual == (False, "parse error\n", 1)

    def test_reports_the_code_a_signal_death_leaves(self, rst: ModuleType) -> None:
        """run_test() should hand back the code the process actually died with.

        A caller that only learns the run was not a success cannot tell a tool
        that refused the source from a tool that crashed on it, and the two
        deserve opposite verdicts for a source the corpus expects refused.
        """
        mock_result = MagicMock(returncode=-11, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            actual = rst.run_test("/fake/test.sv")
        assert actual == (False, "", -11)

    def test_timeout_propagates(self, rst: ModuleType) -> None:
        """run_test() does not catch TimeoutExpired; it propagates."""
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

    def test_simulate_pass_with_assertions(self, rst: ModuleType) -> None:
        """run_test(simulate=True) should pass when exit 0 and assertions pass."""
        mock_result = MagicMock(returncode=0, stdout=":assert: (True)\n", stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            actual = rst.run_test("/fake/test.sv", simulate=True)
        assert actual == (True, "", 0)

    def test_simulate_fail_on_assertion(self, rst: ModuleType) -> None:
        """run_test(simulate=True) should fail when assertion fails."""
        ok, _, _ = _simulate_over_a_failing_assertion(rst)
        assert ok is False

    def test_simulate_names_the_failed_assertion(self, rst: ModuleType) -> None:
        """run_test(simulate=True) should say the assertion is what failed."""
        _, detail, _ = _simulate_over_a_failing_assertion(rst)
        assert "Assertion failed" in detail

    def test_simulate_fail_on_nonzero_exit(self, rst: ModuleType) -> None:
        """run_test(simulate=True) should fail when exit code is non-zero."""
        mock_result = MagicMock(returncode=1, stdout="", stderr="error\n")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            actual = rst.run_test("/fake/test.sv", simulate=True)
        assert actual == (False, "error\n", 1)

    def test_defines_passed_as_dash_d_flags(self, rst: ModuleType) -> None:
        """run_test(defines=...) should include -D flags in the command."""
        cmd = _capture_run_cmd(
            rst, lambda: rst.run_test("/fake/test.sv", defines=["FOO", "BAR=2"]),
        )
        assert _d_flag_values(cmd) == ["FOO", "BAR=2"]


class TestParseMetadata:
    """Tests for the parse_metadata() function."""

    def test_extracts_all_fields(self, rst: ModuleType, tmp_path: Path) -> None:
        """parse_metadata() should extract all key-value pairs."""
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

    def test_returns_empty_dict_when_no_comment(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """parse_metadata() should return {} when no block comment exists."""
        sv = tmp_path / "bare.sv"
        sv.write_text("module bare; endmodule\n")
        assert not rst.parse_metadata(str(sv))

    def test_returns_empty_type_when_absent(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """parse_metadata() should omit 'type' key when not present."""
        sv = tmp_path / "no_type.sv"
        sv.write_text("/*\n:name: no_type\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        assert set(rst.parse_metadata(str(sv))) == {"name", "tags"}


class TestEvalNode:
    """Tests for the eval_node() AST evaluator."""

    def test_constant_true(self, rst: ModuleType) -> None:
        """eval_node() should return True for ast.Constant(True)."""
        assert rst.eval_node(ast.Constant(value=True)) is True

    def test_constant_integer(self, rst: ModuleType) -> None:
        """eval_node() should return the integer value."""
        assert rst.eval_node(ast.Constant(value=42)) == 42

    def test_equality_pass(self, rst: ModuleType) -> None:
        """eval_node() should return True for equal constants."""
        tree = ast.parse("('hello' == 'hello')", mode="eval")
        assert rst.eval_node(tree.body) is True

    def test_equality_fail(self, rst: ModuleType) -> None:
        """eval_node() should return False for unequal constants."""
        tree = ast.parse("(1 == 2)", mode="eval")
        assert rst.eval_node(tree.body) is False

    def test_in_operator(self, rst: ModuleType) -> None:
        """eval_node() should handle the 'in' operator."""
        tree = ast.parse("('est' in 'Test')", mode="eval")
        assert rst.eval_node(tree.body) is True

    def test_not_in_operator(self, rst: ModuleType) -> None:
        """eval_node() should handle the 'not in' operator."""
        tree = ast.parse("('xyz' not in 'Test')", mode="eval")
        assert rst.eval_node(tree.body) is True

    def test_bool_and(self, rst: ModuleType) -> None:
        """eval_node() should handle 'and' boolean operator."""
        tree = ast.parse("(True and True)", mode="eval")
        assert rst.eval_node(tree.body) is True

    def test_bool_or(self, rst: ModuleType) -> None:
        """eval_node() should handle 'or' boolean operator."""
        tree = ast.parse("(False or True)", mode="eval")
        assert rst.eval_node(tree.body) is True

    def test_unary_not(self, rst: ModuleType) -> None:
        """eval_node() should handle unary 'not' operator."""
        tree = ast.parse("(not False)", mode="eval")
        assert rst.eval_node(tree.body) is True

    def test_unsupported_node_raises(self, rst: ModuleType) -> None:
        """eval_node() should raise ValueError for unsupported nodes."""
        raised = False
        try:
            rst.eval_node(ast.Name(id="x"))
        except ValueError:
            raised = True
        assert raised


def _check_without_ast(rst: ModuleType, line: str) -> tuple[bool, str]:
    """Run check_assertions() over line with ast.parse refusing to parse."""
    with patch("ast.parse", side_effect=SyntaxError):
        outcome: tuple[bool, str] = rst.check_assertions(line)
    return outcome


class TestCheckAssertions:
    """Tests for the check_assertions() function."""

    def test_passing_assertion(self, rst: ModuleType) -> None:
        """check_assertions() should return (True, '') for passing assert."""
        assert rst.check_assertions(":assert: (True)") == (True, "")

    def test_failing_assertion(self, rst: ModuleType) -> None:
        """check_assertions() should return False for a failing assert."""
        assert rst.check_assertions(":assert: (1 == 2)")[0] is False

    def test_failing_assertion_names_the_failure(self, rst: ModuleType) -> None:
        """check_assertions() should say the assertion is what failed."""
        assert "Assertion failed" in rst.check_assertions(":assert: (1 == 2)")[1]

    def test_no_assertions_passes(self, rst: ModuleType) -> None:
        """check_assertions() should pass when stdout has no :assert: lines."""
        assert rst.check_assertions("hello world\n") == (True, "")

    def test_multiple_assertions_all_pass(self, rst: ModuleType) -> None:
        """check_assertions() should pass when all assertions pass."""
        stdout = ":assert: (True)\n:assert: (1 == 1)\n"
        assert rst.check_assertions(stdout) == (True, "")

    def test_multiple_assertions_one_fails(self, rst: ModuleType) -> None:
        """check_assertions() should fail on the first failing assertion."""
        stdout = ":assert: (True)\n:assert: (1 == 2)\n"
        ok, _ = rst.check_assertions(stdout)
        assert ok is False

    def test_syntax_error_fails(self, rst: ModuleType) -> None:
        """check_assertions() should fail on malformed expression."""
        assert rst.check_assertions(":assert: (!!!)")[0] is False

    def test_syntax_error_names_the_parse_failure(self, rst: ModuleType) -> None:
        """check_assertions() should say a malformed expression would not parse."""
        assert "Assertion parse error" in rst.check_assertions(":assert: (!!!)")[1]

    def test_string_equality_pass(self, rst: ModuleType) -> None:
        """try_string_equality() should return True for matching strings."""
        assert rst.try_string_equality("('hello' == 'hello')") is True

    def test_string_equality_fail(self, rst: ModuleType) -> None:
        """try_string_equality() should return False for mismatched strings."""
        assert rst.try_string_equality("('hello' == 'world')") is False

    def test_string_equality_fallback_pass(self, rst: ModuleType) -> None:
        """check_assertions() should pass via string fallback on ast failure."""
        assert _check_without_ast(rst, ":assert: ('same' == 'same')") == (True, "")

    def test_string_equality_fallback_fail(self, rst: ModuleType) -> None:
        """check_assertions() should fail via string fallback on mismatch."""
        assert _check_without_ast(rst, ":assert: ('abc' == 'xyz')")[0] is False

    def test_string_equality_fallback_names_the_failure(
        self, rst: ModuleType,
    ) -> None:
        """The string fallback should say the assertion is what failed."""
        detail = _check_without_ast(rst, ":assert: ('abc' == 'xyz')")[1]
        assert "Assertion failed" in detail


def test_chapter_from_path_extracts_chapter_directory(rst: ModuleType) -> None:
    """chapter_from_path() should return the parent directory name."""
    assert rst.chapter_from_path("/a/chapter-5/foo.sv") == "chapter-5"


def test_chapter_from_path_falls_back_to_parent_name(rst: ModuleType) -> None:
    """chapter_from_path() should return parent dir when no chapter- part."""
    assert rst.chapter_from_path("/some/other/foo.sv") == "other"


def test_print_chapter_breakdown_has_box_drawing_table(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """print_chapter_breakdown() should print a box-drawing table."""
    results = [{"chapter": "chapter-5", "status": "pass"}]
    rst.print_chapter_breakdown(results)
    captured = capsys.readouterr().out
    assert all(
        s in captured
        for s in ("┌", "┐", "├", "┤", "└", "┘", "│",
                   "Clause", "# of tests", "Failed", "Percentage")
    )


def test_print_chapter_breakdown_shows_correct_values(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """print_chapter_breakdown() should show tests, passed, failed, and pct."""
    results = [
        {"chapter": "chapter-5", "status": "pass"},
        {"chapter": "chapter-5", "status": "fail"},
        {"chapter": "chapter-6", "status": "pass"},
    ]
    rst.print_chapter_breakdown(results)
    captured = re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)
    # Column order: Clause │ # of tests │ Failed │ Percentage.
    row5 = next(ln for ln in captured.splitlines() if ln.startswith("│ 5"))
    row6 = next(ln for ln in captured.splitlines() if ln.startswith("│ 6"))
    cells5 = [c.strip() for c in row5.strip("│").split("│")]
    cells6 = [c.strip() for c in row6.strip("│").split("│")]
    assert [cells5, cells6] == [
        ["5", "2", "1", "50.0%"], ["6", "1", "0", "100.0%"],
    ]


def test_print_chapter_breakdown_uses_natural_order(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """print_chapter_breakdown() should list 5 before 25 (natural order)."""
    results = [
        {"chapter": "chapter-25", "status": "pass"},
        {"chapter": "chapter-5", "status": "pass"},
    ]
    rst.print_chapter_breakdown(results)
    captured = re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)
    # Chapter column shows just the number, not "chapter-N".
    assert captured.index("│ 5") < captured.index("│ 25")


def _score_expected_rejection(
    rst: ModuleType, tmp_path: Path, returncode: int, stderr: str,
    tags: str = "5.10",
) -> tuple[dict[str, Any], int]:
    """Score a file the corpus marks ``should_fail_because`` and tags *tags*.

    The stubbed tool leaves *returncode* and *stderr* behind, which together
    with the tag is the whole of what the runner has to reach a verdict on.
    An empty *tags* writes a file carrying no ``:tags:`` field at all.
    """
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
    """Score a file whose ``:type:`` names simulation and whose assertion holds.

    The command the stubbed tool was asked to run comes back beside the
    result, so a test about which mode was chosen can read it.
    """
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
    """Tests for the build_result() function."""

    def test_pass_returns_correct_dict(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should return result dict with status=pass."""
        sv = tmp_path / "chapter-5" / "foo.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: foo\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, ok = rst.build_result(str(sv))
        verdict = (ok, result["name"], result["chapter"], result["status"])
        assert verdict == (1, "5.10--foo.sv", "chapter-5", "pass")

    def test_fail_returns_correct_dict(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should return result dict with status=fail."""
        sv = tmp_path / "chapter-5" / "bar.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: bar\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=1, stderr="error\n")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, ok = rst.build_result(str(sv))
        assert (ok, result["status"]) == (0, "fail")

    def test_timeout_returns_timeout_status(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should return status=timeout on TimeoutExpired."""
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
        """A tool that refused the file, and said why, judged it as asked."""
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1, "xfail.sv:1:1: error: redeclaration of 'v'\n",
        )
        assert (ok, result["status"]) == (1, "pass")

    def test_signal_death_does_not_score_a_pass_for_an_expected_rejection(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A tool that died on the file never judged it.

        Every way of not exiting zero used to invert into a pass, so a crash
        was counted as the file conforming to the clause it was written for.
        """
        result, ok = _score_expected_rejection(rst, tmp_path, -11, "")
        assert (ok, result["status"]) == (0, "fail")

    def test_exit_one_with_no_diagnostic_does_not_score_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A refusal that names no reason is not a refusal that was reasoned."""
        result, ok = _score_expected_rejection(rst, tmp_path, 1, "")
        assert (ok, result["status"]) == (0, "fail")

    def test_acceptance_does_not_score_a_pass_for_an_expected_rejection(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A file the corpus says is illegal, and the tool took, is a failure."""
        result, ok = _score_expected_rejection(rst, tmp_path, 0, "")
        assert (ok, result["status"]) == (0, "fail")

    def test_expected_rejection_carries_should_fail_into_the_result(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should record that rejection was the expected outcome.

        The status alone says pass for a file the tool accepted and for a file
        the tool rejected on purpose, so whatever reads the result afterwards
        cannot tell the two apart unless the metadata reaches it.
        """
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
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should pass :defines: metadata as -D flags."""
        sv = tmp_path / "chapter-5" / "defs.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: defs\n:tags: 5.6.4\n"
            ":defines: TEST_VAR VAR_1=2\n*/\nmodule m; endmodule\n"
        )
        cmd = _capture_run_cmd(rst, lambda: rst.build_result(str(sv)))
        assert _d_flag_values(cmd) == ["TEST_VAR", "VAR_1=2"]

    def test_simulation_mode_used_for_simulation_type(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should run simulation when type contains 'simulation'."""
        cmd = _build_result_over_a_simulation_file(rst, tmp_path)[2]
        assert "--lint-only" not in cmd

    def test_a_simulated_file_whose_assertions_hold_scores_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should pass a simulated file whose assertions held."""
        result, ok, _ = _build_result_over_a_simulation_file(rst, tmp_path)
        assert (ok, result["status"]) == (1, "pass")

    def test_name_includes_clause_number_from_tags(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should prepend first tag when name lacks clause number."""
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

    def test_name_skips_clause_when_already_present(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should not double-prefix when filename starts with clause."""
        sv = tmp_path / "chapter-5" / "5.6.4--compiler-directives-define.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: define\n:tags: 5.6.4\n*/\nmodule m; endmodule\n"
        )
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result):
            result, _ = rst.build_result(str(sv))
        assert result["name"] == "5.6.4--compiler-directives-define.sv"

    def test_name_omits_clause_when_no_tags(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should use bare path when no tags metadata."""
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
        """Run build_result with parse_metadata raising OSError."""
        sv = tmp_path / "chapter-5" / "bad.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: bad\n*/\nmodule m; endmodule\n")
        with patch.object(
            rst, "parse_metadata",
            side_effect=OSError("read error"),
        ):
            result: tuple[dict[str, Any], int] = rst.build_result(str(sv))
            return result

    def test_exception_returns_ok_zero(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should return ok=0 when an exception is caught."""
        _, ok = self._build_result_with_oserror(rst, tmp_path)
        assert ok == 0

    def test_exception_returns_fail_status(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should return fail status when an exception is caught."""
        result, _ = self._build_result_with_oserror(rst, tmp_path)
        assert result["status"] == "fail"

    def test_exception_captures_stderr(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should capture exception details in stderr field."""
        result, _ = self._build_result_with_oserror(rst, tmp_path)
        assert "OSError: read error" in result["stderr"]

    def test_exception_logs_to_stderr(
        self,
        rst: ModuleType,
        tmp_path: Path,
        capsys: pytest.CaptureFixture[str],
    ) -> None:
        """build_result() should log caught exceptions to stderr."""
        self._build_result_with_oserror(rst, tmp_path)
        assert "read error" in capsys.readouterr().err


class TestScoringARejectionAgainstTheTag:
    """Tests for build_result() scoring a rejection against the file's clause tag.

    Every file in the sv-tests corpus records the clause it exercises in its
    ``:tags:`` field, which is the corpus authors' own statement of what
    running that file tests. A file marked ``should_fail_because`` scores a
    pass only when deltahdl rejected it under that clause.
    """

    def test_rejection_naming_the_tagged_clause_scores_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A file rejected under the clause it is tagged with tested that clause."""
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1,
            "xfail.sv:1:1: error: enum has an x assignment (§6.19)\n",
            "6.19",
        )
        assert (ok, result["status"]) == (1, "pass")

    def test_rejection_naming_a_different_clause_does_not_score_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A file rejected under another clause never exercised its own.

        A rejection enforcing §7.3 for a file tagged §6.19 leaves §6.19
        untested, and scoring it a pass reports the corpus as covering a
        clause it never reached.
        """
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1,
            "xfail.sv:1:1: error: net type mismatch (§7.3)\n",
            "6.19",
        )
        assert (ok, result["status"]) == (0, "fail")

    def test_rejection_naming_no_clause_scores_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A rejection naming no clause is scored as it was before tags were read.

        The 26 sites under src/ that build a report with Subclause::None()
        state a fact about the run rather than a breach of the standard, so
        there is no clause to compare the tag against.
        """
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1,
            "xfail.sv:1:1: error: cannot open include file 'x.svh'\n",
            "6.19",
        )
        assert (ok, result["status"]) == (1, "pass")

    def test_rejection_for_a_file_with_no_clause_tag_scores_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A file carrying no clause tag is scored on the rejection alone.

        Three corpus files marked should_fail_because tag ``uvm-random uvm``
        and name no clause, and failing them for a comparison that was never
        available would fail them for how the corpus is written.
        """
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1,
            "xfail.sv:1:1: error: net type mismatch (§7.3)\n",
            "",
        )
        assert (ok, result["status"]) == (1, "pass")

    def test_subclause_of_the_tagged_clause_scores_a_pass(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """A file tagged with a clause is exercising the subclauses under it.

        32 of the 71 tagged files name a clause one level deep, and the
        diagnostic that rejects such a file is free to enforce a rule stated
        further down.
        """
        result, ok = _score_expected_rejection(
            rst, tmp_path, 1,
            "xfail.sv:1:1: error: bad randomize() call (§16.12.17)\n",
            "16.12",
        )
        assert (ok, result["status"]) == (1, "pass")

    def test_the_tagged_clause_reaches_the_result(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """build_result() should record the clause the corpus tags the file with.

        print_reason() names the expected clause beside the reported one when
        they disagree, and the metadata is not parsed a second time.
        """
        result, _ = _score_expected_rejection(
            rst, tmp_path, 1,
            "xfail.sv:1:1: error: enum has an x assignment (§6.19)\n",
            "6.19",
        )
        assert result["clause"] == "6.19"


def _print_status_for_a_clause_mismatch(rst: ModuleType) -> None:
    """Print a file tagged §6.19 that was rejected under §7.3 instead."""
    rst.print_status(
        {"name": "y.sv", "status": "fail", "should_fail": True,
         "stderr": "y.sv:4:2: error: net type mismatch (§7.3)",
         "returncode": 1, "clause": "6.19"},
        0,
    )


class TestPrintStatus:
    """Tests for the print_status() function."""

    def test_prints_pass(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """print_status() should print PASS for passing tests."""
        rst.print_status({"name": "x.sv", "status": "pass"}, 1)
        assert "PASS" in capsys.readouterr().out

    def test_prints_fail(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """print_status() should print FAIL for failing tests."""
        rst.print_status({"name": "x.sv", "status": "fail"}, 0)
        assert "FAIL" in capsys.readouterr().out

    def test_prints_timeout(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """print_status() should print TIMEOUT for timed-out tests."""
        rst.print_status({"name": "x.sv", "status": "timeout"}, 0)
        assert "TIMEOUT" in capsys.readouterr().out

    def test_prints_what_the_tool_said_about_a_failure(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A failing test carries the tool's own account of it."""
        rst.print_status(
            {"name": "x.sv", "status": "fail", "stderr": "x.sv:3:1: error: no"},
            0,
        )
        assert "x.sv:3:1: error: no" in capsys.readouterr().out

    def test_says_nothing_about_an_ordinary_pass(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A file the tool was meant to accept, and did, has nothing to answer for."""
        rst.print_status(
            {"name": "x.sv", "status": "pass", "should_fail": False,
             "stderr": "x.sv:3:1: error: no"},
            1,
        )
        assert "error" not in capsys.readouterr().out

    def test_prints_what_the_tool_said_about_an_expected_rejection(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A file that passed by being rejected passed because of what was said.

        The complaint is the whole evidence that the file tested the rule it
        names, so a reader who cannot see it cannot tell the rejection the file
        was written for from an unrelated one that scores the same pass.
        """
        rst.print_status(
            {"name": "y.sv", "status": "pass", "should_fail": True,
             "stderr": "y.sv:4:2: error: redeclaration of 'v'"},
            1,
        )
        assert "y.sv:4:2: error: redeclaration of 'v'" in capsys.readouterr().out

    def test_prints_the_exit_code_when_an_expected_rejection_crashed(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A tool that died on a file usually leaves nothing else to read.

        Without the code the run says only that the file did not pass, which
        reads the same as the tool having calmly accepted a file it should
        have refused. The two are opposite findings.
        """
        rst.print_status(
            {"name": "z.sv", "status": "fail", "should_fail": True,
             "stderr": "", "returncode": -11},
            0,
        )
        assert "-11" in capsys.readouterr().out

    def test_says_nothing_extra_when_an_expected_rejection_was_accepted(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """An exit of zero is the tool accepting the file, which FAIL says."""
        rst.print_status(
            {"name": "z.sv", "status": "fail", "should_fail": True,
             "stderr": "", "returncode": 0},
            0,
        )
        assert "exited" not in capsys.readouterr().out

    def test_prints_both_clauses_when_the_rejection_names_another(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A rejection under another clause reads as the pass it is not.

        The tool refused the file and said why, which is what a file marked
        should_fail_because passes on. Only the two clause numbers side by
        side show why this one failed, so both are printed.
        """
        _print_status_for_a_clause_mismatch(rst)
        out = capsys.readouterr().out
        assert all(clause in out for clause in ("7.3", "6.19"))

    def test_says_nothing_about_the_exit_code_when_the_clauses_disagree(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """The two clause numbers are the finding, so the exit code is not one."""
        _print_status_for_a_clause_mismatch(rst)
        assert "exited" not in capsys.readouterr().out

    def test_prints_the_exit_code_when_the_tagged_clause_was_named(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """A tool that named the tagged clause and then died still died.

        The rejection matches the tag, so there is no mismatch to report and
        the exit code is again the only thing separating a crash from the
        tool having calmly accepted a file it should have refused.
        """
        rst.print_status(
            {"name": "z.sv", "status": "fail", "should_fail": True,
             "stderr": "z.sv:1:1: error: enum has an x assignment (§6.19)",
             "returncode": -11, "clause": "6.19"},
            0,
        )
        assert "-11" in capsys.readouterr().out

    def test_prints_what_the_tool_said_before_a_timeout(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """What a test managed to say before it hung is the evidence there is."""
        rst.print_status(
            {"name": "x.sv", "status": "timeout", "stderr": "elaborating top"},
            0,
        )
        assert "elaborating top" in capsys.readouterr().out


class TestWriteJunitXml:
    """Tests for the write_junit_xml() function."""

    def _make_results(self) -> list[dict[str, Any]]:
        """Create a sample results list with pass, fail, and timeout."""
        return [
            {"name": "a.sv", "chapter": "chapter-5", "status": "pass",
             "time": 0.1, "stderr": ""},
            {"name": "b.sv", "chapter": "chapter-5", "status": "fail",
             "time": 0.2, "stderr": "error msg"},
            {"name": "c.sv", "chapter": "chapter-6", "status": "timeout",
             "time": 30.0, "stderr": ""},
        ]

    def test_correct_suite_attributes(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """write_junit_xml() should set tests/failures/errors attributes."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        rst.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        root = tree.getroot()
        assert (
            root.tag,
            root.attrib["tests"],
            root.attrib["failures"],
            root.attrib["errors"],
        ) == ("testsuite", "3", "1", "1")

    def test_failure_elements_present(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """write_junit_xml() should include <failure> for failed tests."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        rst.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        failures = tree.findall(".//failure")
        assert [(f.attrib["message"], f.text) for f in failures] == [
            ("b.sv failed lint", "error msg"),
        ]

    def test_error_elements_present(
        self, rst: ModuleType, tmp_path: Path,
    ) -> None:
        """write_junit_xml() should include <error> for timed-out tests."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        rst.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        errors = tree.findall(".//error")
        assert [(e.attrib["message"], e.text) for e in errors] == [
            ("c.sv timed out", "Process exceeded 30s timeout."),
        ]


class TestMainBrokenPipe:
    """Tests for BrokenPipeError resilience in main()."""

    _FAKE_RESULT = (
        {"name": "a.sv", "chapter": "chapter-5", "status": "pass",
         "time": 0.1, "stderr": ""},
        1,
    )

    def _run_with_broken_pipe(self, rst: ModuleType, argv: list[str]) -> None:
        """Run main() with print_status raising BrokenPipeError."""
        with patch("sys.argv", argv), \
             patch.object(rst, "check_binary"), \
             patch.object(rst.glob, "glob", return_value=["/x/a.sv"]), \
             patch.object(rst, "build_result", return_value=self._FAKE_RESULT), \
             patch.object(rst, "print_status", side_effect=BrokenPipeError), \
             patch.object(rst.os, "open", return_value=99), \
             patch.object(rst.os, "dup2"), \
             patch.object(rst.os, "close"):
            rst.main()

    def test_main_exits_one_on_broken_pipe(
        self,
        rst: ModuleType,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() should exit 1 when stdout pipe breaks."""
        assert get_exit_code(
            lambda: self._run_with_broken_pipe(rst, ["run_sv_tests.py"])
        ) == 1

    def test_main_prints_diagnostic_on_broken_pipe(
        self,
        rst: ModuleType,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() should print runner bug diagnostic to stderr."""
        stderr = io.StringIO()
        with patch("sys.stderr", stderr):
            get_exit_code(
                lambda: self._run_with_broken_pipe(rst, ["run_sv_tests.py"])
            )
        assert "actions/runner/issues/2684" in stderr.getvalue()

    def test_main_skips_junit_xml_on_broken_pipe(
        self,
        rst: ModuleType,
        tmp_path: Path,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() should not write JUnit XML when stdout pipe breaks."""
        xml_path = str(tmp_path / "pipe-report.xml")
        get_exit_code(
            lambda: self._run_with_broken_pipe(
                rst, ["run_sv_tests.py", "--junit-xml", xml_path]
            )
        )
        assert not tmp_path.joinpath("pipe-report.xml").exists()


class TestCorpusRevision:
    """Tests for the corpus_revision() function."""

    _SHA = "3d9f0c47a1be82605fd3ca9b71e4d85216a8c3f2"

    def test_returns_the_commit_git_reports(self, rst: ModuleType) -> None:
        """corpus_revision() should return the commit git named, stripped."""
        stub = MagicMock(returncode=0, stdout=f"  {self._SHA}\n  ")
        with patch.object(rst.subprocess, "run", return_value=stub):
            assert rst.corpus_revision() == self._SHA

    def test_invokes_git_against_the_test_directory(self, rst: ModuleType) -> None:
        """corpus_revision() should ask git about the sv-tests checkout.

        Asking about the working directory instead reports the commit of
        whatever repository the run was started from, which is a commit the
        corpus never had.
        """
        assert _capture_run_cmd(rst, rst.corpus_revision) == [
            "git", "-C", str(rst.TEST_DIR), "rev-parse", "HEAD",
        ]

    def test_returns_unknown_when_git_fails(self, rst: ModuleType) -> None:
        """corpus_revision() should report unknown when git exits non-zero."""
        stub = MagicMock(returncode=128, stdout="")
        with patch.object(rst.subprocess, "run", return_value=stub):
            assert rst.corpus_revision() == "unknown"

    def test_returns_unknown_when_git_is_absent(self, rst: ModuleType) -> None:
        """corpus_revision() should report unknown when git cannot be run."""
        with patch.object(
            rst.subprocess, "run", side_effect=FileNotFoundError,
        ):
            assert rst.corpus_revision() == "unknown"
