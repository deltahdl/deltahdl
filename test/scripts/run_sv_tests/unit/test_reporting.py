import io
import re
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest

CaptureRunCmd = Callable[[ModuleType, Callable[[], Any]], list[str]]


def test_chapter_from_path_extracts_chapter_directory(rst: ModuleType) -> None:
    assert rst.chapter_from_path("/a/chapter-5/foo.sv") == "chapter-5"


def test_chapter_from_path_falls_back_to_parent_name(rst: ModuleType) -> None:
    assert rst.chapter_from_path("/some/other/foo.sv") == "other"


def test_print_chapter_breakdown_has_box_drawing_table(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    results = [{"chapter": "chapter-5", "status": "pass"}]
    rst.print_chapter_breakdown(results)
    captured = capsys.readouterr().out
    assert all(
        s in captured
        for s in ("┌", "┐", "├", "┤", "└", "┘", "│",
                   "Clause", "# of tests", "Failed")
    )


def test_print_chapter_breakdown_has_no_percentage_column(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    results = [
        {"chapter": "chapter-5", "status": "pass"},
        {"chapter": "chapter-5", "status": "fail"},
    ]
    rst.print_chapter_breakdown(results)
    captured = capsys.readouterr().out
    assert not any(s in captured for s in ("Percentage", "%"))


def test_print_chapter_breakdown_shows_correct_values(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    results = [
        {"chapter": "chapter-5", "status": "pass"},
        {"chapter": "chapter-5", "status": "fail"},
        {"chapter": "chapter-6", "status": "pass"},
    ]
    rst.print_chapter_breakdown(results)
    captured = re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)
    row5 = next(ln for ln in captured.splitlines() if ln.startswith("│ 5"))
    row6 = next(ln for ln in captured.splitlines() if ln.startswith("│ 6"))
    cells5 = [c.strip() for c in row5.strip("│").split("│")]
    cells6 = [c.strip() for c in row6.strip("│").split("│")]
    assert [cells5, cells6] == [["5", "2", "1"], ["6", "1", "0"]]


def test_print_chapter_breakdown_uses_natural_order(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    results = [
        {"chapter": "chapter-25", "status": "pass"},
        {"chapter": "chapter-5", "status": "pass"},
    ]
    rst.print_chapter_breakdown(results)
    captured = re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)
    assert captured.index("│ 5") < captured.index("│ 25")


def _print_status_for_a_clause_mismatch(rst: ModuleType) -> None:
    rst.print_status(
        {"name": "y.sv", "status": "fail", "should_fail": True,
         "stderr": "y.sv:4:2: error: net type mismatch (§7.3)",
         "returncode": 1, "clause": "6.19"},
        0,
    )


def test_prints_pass(rst: ModuleType, capsys: pytest.CaptureFixture[str]) -> None:
    rst.print_status({"name": "x.sv", "status": "pass"}, 1)
    assert "PASS" in capsys.readouterr().out


def test_prints_fail(rst: ModuleType, capsys: pytest.CaptureFixture[str]) -> None:
    rst.print_status({"name": "x.sv", "status": "fail"}, 0)
    assert "FAIL" in capsys.readouterr().out


def test_prints_timeout(rst: ModuleType, capsys: pytest.CaptureFixture[str]) -> None:
    rst.print_status({"name": "x.sv", "status": "timeout"}, 0)
    assert "TIMEOUT" in capsys.readouterr().out


def test_prints_what_the_tool_said_about_a_failure(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "x.sv", "status": "fail", "stderr": "x.sv:3:1: error: no"},
        0,
    )
    assert "x.sv:3:1: error: no" in capsys.readouterr().out


def test_says_nothing_about_an_ordinary_pass(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "x.sv", "status": "pass", "should_fail": False,
         "stderr": "x.sv:3:1: error: no"},
        1,
    )
    assert "error" not in capsys.readouterr().out


def test_prints_what_the_tool_said_about_an_expected_rejection(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "y.sv", "status": "pass", "should_fail": True,
         "stderr": "y.sv:4:2: error: redeclaration of 'v'"},
        1,
    )
    assert "y.sv:4:2: error: redeclaration of 'v'" in capsys.readouterr().out


def test_prints_the_exit_code_when_an_expected_rejection_crashed(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "z.sv", "status": "fail", "should_fail": True,
         "stderr": "", "returncode": -11},
        0,
    )
    assert (
        "    deltahdl exited -11 without rejecting the code\n"
        in capsys.readouterr().out
    )


def test_says_nothing_extra_when_an_expected_rejection_was_accepted(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "z.sv", "status": "fail", "should_fail": True,
         "stderr": "", "returncode": 0},
        0,
    )
    assert "exited" not in capsys.readouterr().out


def test_prints_both_clauses_when_the_rejection_names_another(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _print_status_for_a_clause_mismatch(rst)
    assert (
        "    deltahdl rejected the code under §7.3, but the test's tag names §6.19\n"
        in capsys.readouterr().out
    )


def test_prints_the_tag_and_its_2023_subclause_when_the_tag_is_renumbered(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "y.sv", "status": "fail", "should_fail": True,
         "stderr": "y.sv:4:2: error: static constraint block (§18.5.10)",
         "returncode": 1, "clause": "18.5.10"},
        0,
    )
    assert (
        "    deltahdl rejected the code under §18.5.10, but the test's tag"
        " 18.5.10 names §18.5.9\n"
        in capsys.readouterr().out
    )


def test_says_nothing_about_the_exit_code_when_the_clauses_disagree(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _print_status_for_a_clause_mismatch(rst)
    assert "exited" not in capsys.readouterr().out


def test_prints_the_exit_code_when_the_tagged_clause_was_named(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "z.sv", "status": "fail", "should_fail": True,
         "stderr": "z.sv:1:1: error: enum has an x assignment (§6.19)",
         "returncode": -11, "clause": "6.19"},
        0,
    )
    assert "-11" in capsys.readouterr().out


def test_prints_what_the_tool_said_before_a_timeout(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    rst.print_status(
        {"name": "x.sv", "status": "timeout", "stderr": "elaborating top"},
        0,
    )
    assert "elaborating top" in capsys.readouterr().out


class TestWriteJunitXml:
    def _make_results(self) -> list[dict[str, Any]]:
        return [
            {"name": "a.sv", "chapter": "chapter-5", "status": "pass",
             "time": 0.1, "stderr": ""},
            {"name": "b.sv", "chapter": "chapter-5", "status": "fail",
             "time": 0.2, "stderr": "error msg"},
            {"name": "c.sv", "chapter": "chapter-6", "status": "timeout",
             "time": 30.0, "stderr": ""},
        ]

    def test_correct_suite_attributes(self, rst: ModuleType, tmp_path: Path) -> None:
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

    def test_failure_elements_present(self, rst: ModuleType, tmp_path: Path) -> None:
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        rst.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        failures = tree.findall(".//failure")
        assert [(f.attrib["message"], f.text) for f in failures] == [
            ("b.sv failed lint", "error msg"),
        ]

    def test_error_elements_present(self, rst: ModuleType, tmp_path: Path) -> None:
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        rst.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        errors = tree.findall(".//error")
        assert [(e.attrib["message"], e.text) for e in errors] == [
            ("c.sv timed out", "Process exceeded 30s timeout."),
        ]


class TestMainBrokenPipe:
    _FAKE_RESULT = (
        {"name": "a.sv", "chapter": "chapter-5", "status": "pass",
         "time": 0.1, "stderr": ""},
        1,
    )

    def _run_with_broken_pipe(self, rst: ModuleType, argv: list[str]) -> None:
        with patch("sys.argv", argv), \
             patch.object(rst, "check_binary"), \
             patch.object(rst.glob, "glob", return_value=["/x/a.sv"]), \
             patch.object(rst, "load_libraries", return_value={}), \
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
        assert get_exit_code(
            lambda: self._run_with_broken_pipe(rst, ["run_sv_tests.py"])
        ) == 1

    def test_main_prints_diagnostic_on_broken_pipe(
        self,
        rst: ModuleType,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
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
        xml_path = str(tmp_path / "pipe-report.xml")
        get_exit_code(
            lambda: self._run_with_broken_pipe(
                rst, ["run_sv_tests.py", "--junit-xml", xml_path]
            )
        )
        assert not tmp_path.joinpath("pipe-report.xml").exists()


class TestSuiteRevision:
    _SHA = "3d9f0c47a1be82605fd3ca9b71e4d85216a8c3f2"

    def test_returns_the_commit_git_reports(self, rst: ModuleType) -> None:
        stub = MagicMock(returncode=0, stdout=f"  {self._SHA}\n  ")
        with patch.object(rst.subprocess, "run", return_value=stub):
            assert rst.suite_revision() == self._SHA

    def test_invokes_git_against_the_test_directory(
        self, rst: ModuleType, capture_run_cmd: CaptureRunCmd,
    ) -> None:
        assert capture_run_cmd(rst, rst.suite_revision) == [
            "git", "-C", str(rst.TEST_DIR), "rev-parse", "HEAD",
        ]

    def test_returns_unknown_when_git_fails(self, rst: ModuleType) -> None:
        stub = MagicMock(returncode=128, stdout="")
        with patch.object(rst.subprocess, "run", return_value=stub):
            assert rst.suite_revision() == "unknown"

    def test_returns_unknown_when_git_is_absent(self, rst: ModuleType) -> None:
        with patch.object(
            rst.subprocess, "run", side_effect=FileNotFoundError,
        ):
            assert rst.suite_revision() == "unknown"
