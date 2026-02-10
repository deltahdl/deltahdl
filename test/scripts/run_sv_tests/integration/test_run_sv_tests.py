"""Integration tests for run_sv_tests module."""

import subprocess
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import run_sv_tests


class TestExecuteSingleTest:
    """Tests for execute_single_test() wiring run_test to print_result."""

    def test_returns_dict_with_all_required_keys(self, capsys):
        """execute_single_test() should return a dict with all required keys."""
        mock_result = MagicMock(returncode=0, stderr="")
        with patch("run_sv_tests.subprocess.run", return_value=mock_result):
            result, ok = run_sv_tests.execute_single_test(
                "/tests/chapter-5/foo.sv"
            )
        assert ok == 1
        required_keys = {"name", "chapter", "status", "time", "stderr"}
        assert required_keys == set(result.keys())
        assert result["name"] == "foo.sv"
        assert result["chapter"] == "chapter-5"
        assert result["status"] == "pass"
        assert result["time"] >= 0
        assert result["stderr"] == ""

        captured = capsys.readouterr().out
        assert "PASS" in captured

    def test_timeout_produces_timeout_status(self, capsys):
        """execute_single_test() should catch TimeoutExpired and set status."""
        with patch(
            "run_sv_tests.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ):
            result, ok = run_sv_tests.execute_single_test(
                "/tests/chapter-5/bar.sv"
            )
        assert ok == 0
        assert result["status"] == "timeout"
        assert result["name"] == "bar.sv"

        captured = capsys.readouterr().out
        assert "TIMEOUT" in captured


class TestCollectAndExecutePipeline:
    """Test the collect_tests -> execute_single_test pipeline."""

    def test_pipeline_produces_correct_result_list(self, capsys):
        """Collecting tests and executing them yields correct result dicts."""
        fake_paths = ["/tests/chapter-5/a.sv", "/tests/chapter-6/b.sv"]
        mock_result = MagicMock(returncode=0, stderr="")

        with patch("run_sv_tests.glob.glob", return_value=fake_paths), \
             patch("run_sv_tests.subprocess.run", return_value=mock_result):
            tests = run_sv_tests.collect_tests()
            results = []
            for path in tests:
                result, _ = run_sv_tests.execute_single_test(path)
                results.append(result)

        assert len(results) == 2
        assert results[0]["name"] == "a.sv"
        assert results[0]["chapter"] == "chapter-5"
        assert results[1]["name"] == "b.sv"
        assert results[1]["chapter"] == "chapter-6"


class TestWriteJunitXmlRoundTrip:
    """Test that write_junit_xml() produces parseable, correct XML."""

    def test_round_trip_preserves_structure(self, tmp_path):
        """Write XML, parse it back, verify full structure."""
        results = [
            {"name": "x.sv", "chapter": "chapter-5", "status": "pass",
             "time": 0.5, "stderr": ""},
            {"name": "y.sv", "chapter": "chapter-5", "status": "fail",
             "time": 0.3, "stderr": "lint error"},
        ]
        filepath = str(tmp_path / "results.xml")
        run_sv_tests.write_junit_xml(results, 1.0, filepath)

        tree = ET.parse(filepath)
        root = tree.getroot()
        assert root.tag == "testsuite"
        assert root.attrib["name"] == "sv-tests"

        testcases = root.findall("testcase")
        assert len(testcases) == 2
        names = [tc.attrib["name"] for tc in testcases]
        assert "x.sv" in names
        assert "y.sv" in names

        # The failing test case should have a <failure> child.
        fail_tc = [tc for tc in testcases if tc.attrib["name"] == "y.sv"][0]
        failures = fail_tc.findall("failure")
        assert len(failures) == 1
        assert failures[0].text == "lint error"


class TestParseArgs:
    """Tests for the parse_args() function."""

    def test_junit_xml_flag(self):
        """parse_args() should set junit_xml when --junit-xml is given."""
        with patch("sys.argv", ["run_sv_tests.py", "--junit-xml", "out.xml"]):
            args = run_sv_tests.parse_args()
        assert args.junit_xml == "out.xml"

    def test_no_flags_defaults_to_none(self):
        """parse_args() with no flags should leave junit_xml as None."""
        with patch("sys.argv", ["run_sv_tests.py"]):
            args = run_sv_tests.parse_args()
        assert args.junit_xml is None
