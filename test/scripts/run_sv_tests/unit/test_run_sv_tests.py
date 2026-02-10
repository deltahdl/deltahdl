"""Unit tests for run_sv_tests module."""

import ast
import re
import subprocess
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import run_sv_tests


class TestCollectTests:
    """Tests for the collect_tests() function."""

    def test_returns_naturally_sorted_paths(self):
        """collect_tests() should use natural sort: chapter-5 before chapter-25."""
        fake_paths = [
            "/x/chapter-25/3-interface.sv",
            "/x/chapter-5/10-arrays.sv",
            "/x/chapter-5/3-types.sv",
            "/x/chapter-26/1-pkg.sv",
        ]
        with patch("run_sv_tests.glob.glob", return_value=fake_paths):
            result = run_sv_tests.collect_tests()
        assert result == [
            "/x/chapter-5/3-types.sv",
            "/x/chapter-5/10-arrays.sv",
            "/x/chapter-25/3-interface.sv",
            "/x/chapter-26/1-pkg.sv",
        ]

    def test_returns_empty_when_no_files(self):
        """collect_tests() should return an empty list when nothing matches."""
        with patch("run_sv_tests.glob.glob", return_value=[]):
            result = run_sv_tests.collect_tests()
        assert result == []


class TestRunTest:
    """Tests for the run_test() function."""

    def test_returns_true_on_exit_zero(self):
        """run_test() should return (True, '') when subprocess exits 0."""
        mock_result = MagicMock(returncode=0, stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            actual = run_sv_tests.run_test("/fake/test.sv")
        assert actual == (True, "")

    def test_returns_false_on_nonzero_exit(self):
        """run_test() should return (False, stderr) on non-zero exit."""
        mock_result = MagicMock(returncode=1, stderr="parse error\n")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            actual = run_sv_tests.run_test("/fake/test.sv")
        assert actual == (False, "parse error\n")

    def test_timeout_propagates(self):
        """run_test() does not catch TimeoutExpired; it propagates."""
        raised = False
        with patch(
            "run_sv_tests.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ):
            try:
                run_sv_tests.run_test("/fake/test.sv")
            except subprocess.TimeoutExpired:
                raised = True
        assert raised

    def test_simulate_pass_with_assertions(self):
        """run_test(simulate=True) should pass when exit 0 and assertions pass."""
        mock_result = MagicMock(returncode=0, stdout=":assert: (True)\n", stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            actual = run_sv_tests.run_test("/fake/test.sv", simulate=True)
        assert actual == (True, "")

    def test_simulate_fail_on_assertion(self):
        """run_test(simulate=True) should fail when assertion fails."""
        mock_result = MagicMock(
            returncode=0, stdout=":assert: (1 == 2)\n", stderr=""
        )
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            ok, detail = run_sv_tests.run_test("/fake/test.sv", simulate=True)
        assert ok is False and "Assertion failed" in detail

    def test_simulate_fail_on_nonzero_exit(self):
        """run_test(simulate=True) should fail when exit code is non-zero."""
        mock_result = MagicMock(returncode=1, stdout="", stderr="error\n")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            actual = run_sv_tests.run_test("/fake/test.sv", simulate=True)
        assert actual == (False, "error\n")

    def test_defines_passed_as_dash_d_flags(self):
        """run_test(defines=...) should include -D flags in the command."""
        mock_result = MagicMock(returncode=0, stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result) as mock_run:
            run_sv_tests.run_test("/fake/test.sv", defines=["FOO", "BAR=2"])
        cmd = mock_run.call_args[0][0]
        assert "-D" in cmd
        foo_idx = cmd.index("-D")
        assert cmd[foo_idx + 1] == "FOO"
        bar_idx = cmd.index("-D", foo_idx + 2)
        assert cmd[bar_idx + 1] == "BAR=2"


class TestParseMetadata:
    """Tests for the parse_metadata() function."""

    def test_extracts_all_fields(self, tmp_path):
        """parse_metadata() should extract all key-value pairs."""
        sv = tmp_path / "test.sv"
        sv.write_text(
            "/*\n:name: foo\n:type: simulation elaboration parsing\n"
            ":tags: 7.3.2\n:should_fail_because: bad code\n*/\n"
            "module top; endmodule\n"
        )
        meta = run_sv_tests.parse_metadata(str(sv))
        assert (
            meta["name"] == "foo"
            and meta["type"] == "simulation elaboration parsing"
            and meta["tags"] == "7.3.2"
            and meta["should_fail_because"] == "bad code"
        )

    def test_returns_empty_dict_when_no_comment(self, tmp_path):
        """parse_metadata() should return {} when no block comment exists."""
        sv = tmp_path / "bare.sv"
        sv.write_text("module bare; endmodule\n")
        assert not run_sv_tests.parse_metadata(str(sv))

    def test_returns_empty_type_when_absent(self, tmp_path):
        """parse_metadata() should omit 'type' key when not present."""
        sv = tmp_path / "no_type.sv"
        sv.write_text("/*\n:name: no_type\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        meta = run_sv_tests.parse_metadata(str(sv))
        assert "name" in meta and "type" not in meta


class TestEvalNode:
    """Tests for the eval_node() AST evaluator."""

    def test_constant_true(self):
        """eval_node() should return True for ast.Constant(True)."""
        assert run_sv_tests.eval_node(ast.Constant(value=True)) is True

    def test_constant_integer(self):
        """eval_node() should return the integer value."""
        assert run_sv_tests.eval_node(ast.Constant(value=42)) == 42

    def test_equality_pass(self):
        """eval_node() should return True for equal constants."""
        tree = ast.parse("('hello' == 'hello')", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is True

    def test_equality_fail(self):
        """eval_node() should return False for unequal constants."""
        tree = ast.parse("(1 == 2)", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is False

    def test_in_operator(self):
        """eval_node() should handle the 'in' operator."""
        tree = ast.parse("('est' in 'Test')", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is True

    def test_not_in_operator(self):
        """eval_node() should handle the 'not in' operator."""
        tree = ast.parse("('xyz' not in 'Test')", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is True

    def test_bool_and(self):
        """eval_node() should handle 'and' boolean operator."""
        tree = ast.parse("(True and True)", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is True

    def test_bool_or(self):
        """eval_node() should handle 'or' boolean operator."""
        tree = ast.parse("(False or True)", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is True

    def test_unary_not(self):
        """eval_node() should handle unary 'not' operator."""
        tree = ast.parse("(not False)", mode="eval")
        assert run_sv_tests.eval_node(tree.body) is True

    def test_unsupported_node_raises(self):
        """eval_node() should raise ValueError for unsupported nodes."""
        raised = False
        try:
            run_sv_tests.eval_node(ast.Name(id="x"))
        except ValueError:
            raised = True
        assert raised


class TestCheckAssertions:
    """Tests for the check_assertions() function."""

    def test_passing_assertion(self):
        """check_assertions() should return (True, '') for passing assert."""
        assert run_sv_tests.check_assertions(":assert: (True)") == (True, "")

    def test_failing_assertion(self):
        """check_assertions() should return (False, detail) for failing assert."""
        ok, detail = run_sv_tests.check_assertions(":assert: (1 == 2)")
        assert ok is False and "Assertion failed" in detail

    def test_no_assertions_passes(self):
        """check_assertions() should pass when stdout has no :assert: lines."""
        assert run_sv_tests.check_assertions("hello world\n") == (True, "")

    def test_multiple_assertions_all_pass(self):
        """check_assertions() should pass when all assertions pass."""
        stdout = ":assert: (True)\n:assert: (1 == 1)\n"
        assert run_sv_tests.check_assertions(stdout) == (True, "")

    def test_multiple_assertions_one_fails(self):
        """check_assertions() should fail on the first failing assertion."""
        stdout = ":assert: (True)\n:assert: (1 == 2)\n"
        ok, _ = run_sv_tests.check_assertions(stdout)
        assert ok is False

    def test_syntax_error_fails(self):
        """check_assertions() should fail on malformed expression."""
        ok, detail = run_sv_tests.check_assertions(":assert: (!!!)")
        assert ok is False and "Assertion error" in detail


def test_chapter_from_path_extracts_chapter_directory():
    """chapter_from_path() should return the parent directory name."""
    assert run_sv_tests.chapter_from_path("/a/chapter-5/foo.sv") == "chapter-5"


def test_print_chapter_breakdown_has_box_drawing_table(capsys):
    """print_chapter_breakdown() should print a box-drawing table."""
    results = [{"chapter": "chapter-5", "status": "pass"}]
    run_sv_tests.print_chapter_breakdown(results)
    captured = capsys.readouterr().out
    assert all(
        s in captured
        for s in ("┌", "┐", "├", "┤", "└", "┘", "│",
                   "Chapter", "Passed", "Sub-Total", "Percentage")
    )


def test_print_chapter_breakdown_shows_correct_values(capsys):
    """print_chapter_breakdown() should show passed, total, and percentage."""
    results = [
        {"chapter": "chapter-5", "status": "pass"},
        {"chapter": "chapter-5", "status": "fail"},
        {"chapter": "chapter-6", "status": "pass"},
    ]
    run_sv_tests.print_chapter_breakdown(results)
    captured = capsys.readouterr().out
    assert "50.0%" in captured and "100.0%" in captured


def test_print_chapter_breakdown_uses_natural_order(capsys):
    """print_chapter_breakdown() should list 5 before 25 (natural order)."""
    results = [
        {"chapter": "chapter-25", "status": "pass"},
        {"chapter": "chapter-5", "status": "pass"},
    ]
    run_sv_tests.print_chapter_breakdown(results)
    captured = re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)
    # Chapter column shows just the number, not "chapter-N".
    assert captured.index("│ 5") < captured.index("│ 25")


class TestBuildResult:
    """Tests for the build_result() function."""

    def test_pass_returns_correct_dict(self, tmp_path):
        """build_result() should return result dict with status=pass."""
        sv = tmp_path / "chapter-5" / "foo.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: foo\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=0, stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            result, ok = run_sv_tests.build_result(str(sv))
        assert (
            ok == 1
            and result["name"] == "foo.sv"
            and result["chapter"] == "chapter-5"
            and result["status"] == "pass"
        )

    def test_fail_returns_correct_dict(self, tmp_path):
        """build_result() should return result dict with status=fail."""
        sv = tmp_path / "chapter-5" / "bar.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: bar\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        mock_result = MagicMock(returncode=1, stderr="error\n")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            result, ok = run_sv_tests.build_result(str(sv))
        assert ok == 0 and result["status"] == "fail"

    def test_timeout_returns_timeout_status(self, tmp_path):
        """build_result() should return status=timeout on TimeoutExpired."""
        sv = tmp_path / "chapter-5" / "slow.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text("/*\n:name: slow\n:tags: 5.10\n*/\nmodule m; endmodule\n")
        with patch(
            "run_sv_tests.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ):
            result, ok = run_sv_tests.build_result(str(sv))
        assert ok == 0 and result["status"] == "timeout"

    def test_should_fail_inverts_failure_to_pass(self, tmp_path):
        """build_result() should invert fail→pass when should_fail_because set."""
        sv = tmp_path / "chapter-5" / "xfail.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: xfail\n:tags: 5.10\n"
            ":should_fail_because: bad code\n*/\nmodule m; endmodule\n"
        )
        mock_result = MagicMock(returncode=1, stderr="error\n")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            result, ok = run_sv_tests.build_result(str(sv))
        assert ok == 1 and result["status"] == "pass"

    def test_should_fail_inverts_pass_to_failure(self, tmp_path):
        """build_result() should invert pass→fail when should_fail_because set."""
        sv = tmp_path / "chapter-5" / "xpass.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: xpass\n:tags: 5.10\n"
            ":should_fail_because: bad code\n*/\nmodule m; endmodule\n"
        )
        mock_result = MagicMock(returncode=0, stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            result, ok = run_sv_tests.build_result(str(sv))
        assert ok == 0 and result["status"] == "fail"

    def test_defines_passed_to_command(self, tmp_path):
        """build_result() should pass :defines: metadata as -D flags."""
        sv = tmp_path / "chapter-5" / "defs.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: defs\n:tags: 5.6.4\n"
            ":defines: TEST_VAR VAR_1=2\n*/\nmodule m; endmodule\n"
        )
        mock_result = MagicMock(returncode=0, stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result) as mock_run:
            run_sv_tests.build_result(str(sv))
        cmd = mock_run.call_args[0][0]
        assert cmd.count("-D") == 2
        d_indices = [i for i, v in enumerate(cmd) if v == "-D"]
        assert cmd[d_indices[0] + 1] == "TEST_VAR"
        assert cmd[d_indices[1] + 1] == "VAR_1=2"

    def test_simulation_mode_used_for_simulation_type(self, tmp_path):
        """build_result() should run simulation when type contains 'simulation'."""
        sv = tmp_path / "chapter-7" / "sim.sv"
        sv.parent.mkdir(parents=True)
        sv.write_text(
            "/*\n:name: sim\n:type: simulation elaboration parsing\n"
            ":tags: 7.3.2\n*/\nmodule m; endmodule\n"
        )
        mock_result = MagicMock(
            returncode=0, stdout=":assert: (True)\n", stderr=""
        )
        with patch("run_sv_tests.subprocess.run", return_value=mock_result) as mock_run:
            result, ok = run_sv_tests.build_result(str(sv))
        assert (
            ok == 1
            and result["status"] == "pass"
            and "--lint-only" not in mock_run.call_args[0][0]
        )


class TestPrintStatus:
    """Tests for the print_status() function."""

    def test_prints_pass(self, capsys):
        """print_status() should print PASS for passing tests."""
        run_sv_tests.print_status({"name": "x.sv", "status": "pass"}, 1)
        assert "PASS" in capsys.readouterr().out

    def test_prints_fail(self, capsys):
        """print_status() should print FAIL for failing tests."""
        run_sv_tests.print_status({"name": "x.sv", "status": "fail"}, 0)
        assert "FAIL" in capsys.readouterr().out

    def test_prints_timeout(self, capsys):
        """print_status() should print TIMEOUT for timed-out tests."""
        run_sv_tests.print_status({"name": "x.sv", "status": "timeout"}, 0)
        assert "TIMEOUT" in capsys.readouterr().out


class TestWriteJunitXml:
    """Tests for the write_junit_xml() function."""

    def _make_results(self):
        """Create a sample results list with pass, fail, and timeout."""
        return [
            {"name": "a.sv", "chapter": "chapter-5", "status": "pass",
             "time": 0.1, "stderr": ""},
            {"name": "b.sv", "chapter": "chapter-5", "status": "fail",
             "time": 0.2, "stderr": "error msg"},
            {"name": "c.sv", "chapter": "chapter-6", "status": "timeout",
             "time": 30.0, "stderr": ""},
        ]

    def test_correct_suite_attributes(self, tmp_path):
        """write_junit_xml() should set tests/failures/errors attributes."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        run_sv_tests.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        root = tree.getroot()
        assert (
            root.tag,
            root.attrib["tests"],
            root.attrib["failures"],
            root.attrib["errors"],
        ) == ("testsuite", "3", "1", "1")

    def test_failure_elements_present(self, tmp_path):
        """write_junit_xml() should include <failure> for failed tests."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        run_sv_tests.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        failures = tree.findall(".//failure")
        assert (
            len(failures) == 1
            and "b.sv" in failures[0].attrib["message"]
            and failures[0].text == "error msg"
        )

    def test_error_elements_present(self, tmp_path):
        """write_junit_xml() should include <error> for timed-out tests."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        run_sv_tests.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        errors = tree.findall(".//error")
        assert (
            len(errors) == 1
            and "c.sv" in errors[0].attrib["message"]
            and "30s timeout" in errors[0].text
        )
