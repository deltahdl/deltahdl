"""Unit tests for what run_sv_tests reports of a run.

The cases over what the runner does with a corpus file are in
test_run_sv_tests.py, which the 1000-line cap pylint imposes on a module
separated this file from. The division is by subject: everything here reads
what a finished run prints or writes -- the chapter breakdown, the per-file
status line, the JUnit XML, the broken pipe a reader closing early produces,
and the corpus revision a count was measured over -- and nothing here runs a
corpus file.
"""

import io
import re
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest

# The helper the capture_run_cmd fixture in ../conftest.py hands back.
CaptureRunCmd = Callable[[ModuleType, Callable[[], Any]], list[str]]


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

    def test_invokes_git_against_the_test_directory(
        self, rst: ModuleType, capture_run_cmd: CaptureRunCmd,
    ) -> None:
        """corpus_revision() should ask git about the sv-tests checkout.

        Asking about the working directory instead reports the commit of
        whatever repository the run was started from, which is a commit the
        corpus never had.
        """
        assert capture_run_cmd(rst, rst.corpus_revision) == [
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
