"""Unit tests for run_sv_tests module."""

import subprocess
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest

import run_sv_tests


class TestCollectTests:
    """Tests for the collect_tests() function."""

    def test_returns_sorted_paths(self):
        """collect_tests() should return sorted paths matching the glob."""
        fake_paths = ["/x/chapter-6/b.sv", "/x/chapter-5/a.sv"]
        with patch("run_sv_tests.glob.glob", return_value=fake_paths):
            result = run_sv_tests.collect_tests()
        assert result == sorted(fake_paths)

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
            passed, stderr = run_sv_tests.run_test("/fake/test.sv")
        assert passed is True
        assert stderr == ""

    def test_returns_false_on_nonzero_exit(self):
        """run_test() should return (False, stderr) on non-zero exit."""
        mock_result = MagicMock(returncode=1, stderr="parse error\n")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            passed, stderr = run_sv_tests.run_test("/fake/test.sv")
        assert passed is False
        assert stderr == "parse error\n"

    def test_timeout_propagates(self):
        """run_test() does not catch TimeoutExpired; it propagates."""
        with patch(
            "run_sv_tests.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ):
            with pytest.raises(subprocess.TimeoutExpired):
                run_sv_tests.run_test("/fake/test.sv")


class TestChapterFromPath:
    """Tests for the chapter_from_path() function."""

    def test_extracts_chapter_directory(self):
        """chapter_from_path() should return the parent directory name."""
        assert run_sv_tests.chapter_from_path("/a/chapter-5/foo.sv") == "chapter-5"


class TestPrintChapterBreakdown:
    """Tests for the print_chapter_breakdown() function."""

    def test_groups_pass_fail_by_chapter(self, capsys):
        """print_chapter_breakdown() should print per-chapter counts."""
        results = [
            {"chapter": "chapter-5", "status": "pass"},
            {"chapter": "chapter-5", "status": "fail"},
            {"chapter": "chapter-6", "status": "pass"},
        ]
        run_sv_tests.print_chapter_breakdown(results)
        captured = capsys.readouterr().out
        assert "chapter-5: 1/2 passed" in captured
        assert "chapter-6: 1/1 passed" in captured


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
        assert root.tag == "testsuite"
        assert root.attrib["tests"] == "3"
        assert root.attrib["failures"] == "1"
        assert root.attrib["errors"] == "1"

    def test_failure_elements_present(self, tmp_path):
        """write_junit_xml() should include <failure> for failed tests."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        run_sv_tests.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        failures = tree.findall(".//failure")
        assert len(failures) == 1
        assert "b.sv" in failures[0].attrib["message"]
        assert failures[0].text == "error msg"

    def test_error_elements_present(self, tmp_path):
        """write_junit_xml() should include <error> for timed-out tests."""
        results = self._make_results()
        filepath = str(tmp_path / "report.xml")
        run_sv_tests.write_junit_xml(results, 5.0, filepath)

        tree = ET.parse(filepath)
        errors = tree.findall(".//error")
        assert len(errors) == 1
        assert "c.sv" in errors[0].attrib["message"]
        assert "30s timeout" in errors[0].text
