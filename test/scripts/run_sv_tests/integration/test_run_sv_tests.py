"""Integration tests for run_sv_tests module."""

import subprocess
from pathlib import Path
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
        captured = capsys.readouterr().out
        assert (
            ok == 1
            and set(result.keys()) == {"name", "chapter", "status", "time", "stderr"}
            and result["name"] == "foo.sv"
            and result["chapter"] == "chapter-5"
            and result["status"] == "pass"
            and result["time"] >= 0
            and result["stderr"] == ""
            and "PASS" in captured
        )

    def test_timeout_produces_timeout_status(self, capsys):
        """execute_single_test() should catch TimeoutExpired and set status."""
        with patch(
            "run_sv_tests.subprocess.run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ):
            result, ok = run_sv_tests.execute_single_test(
                "/tests/chapter-5/bar.sv"
            )
        captured = capsys.readouterr().out
        assert (
            ok == 0
            and result["status"] == "timeout"
            and result["name"] == "bar.sv"
            and "TIMEOUT" in captured
        )


def test_pipeline_produces_correct_result_list():
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

    assert (
        len(results) == 2
        and results[0]["name"] == "a.sv"
        and results[0]["chapter"] == "chapter-5"
        and results[1]["name"] == "b.sv"
        and results[1]["chapter"] == "chapter-6"
    )


def test_write_junit_xml_round_trip_preserves_structure(tmp_path):
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
    testcases = root.findall("testcase")
    names = [tc.attrib["name"] for tc in testcases]
    fail_tc = [tc for tc in testcases if tc.attrib["name"] == "y.sv"][0]
    failures = fail_tc.findall("failure")
    assert (
        root.tag == "testsuite"
        and root.attrib["name"] == "sv-tests"
        and len(testcases) == 2
        and "x.sv" in names
        and "y.sv" in names
        and len(failures) == 1
        and failures[0].text == "lint error"
    )


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


class TestMain:
    """Tests for the main() function."""

    def test_all_pass_exits_zero_with_percentage(self, capsys, get_exit_code):
        """main() exits 0 and summary includes pass percentage."""
        fake_paths = ["/tests/chapter-5/a.sv"]
        mock_result = MagicMock(returncode=0, stderr="")

        def run():
            with patch("sys.argv", ["run_sv_tests.py"]), \
                 patch("run_sv_tests.check_binary"), \
                 patch("run_sv_tests.glob.glob", return_value=fake_paths), \
                 patch("run_sv_tests.subprocess.run", return_value=mock_result):
                run_sv_tests.main()

        assert get_exit_code(run) == 0 and "100.0%" in capsys.readouterr().out

    def test_no_tests_exits_one(self, get_exit_code):
        """main() exits 1 when no .sv files are found."""

        def run():
            with patch("sys.argv", ["run_sv_tests.py"]), \
                 patch("run_sv_tests.check_binary"), \
                 patch("run_sv_tests.glob.glob", return_value=[]):
                run_sv_tests.main()

        assert get_exit_code(run) == 1

    def test_writes_junit_xml(self, tmp_path, get_exit_code):
        """main() writes JUnit XML when --junit-xml is given."""
        xml_path = str(tmp_path / "report.xml")
        fake_paths = ["/tests/chapter-5/a.sv"]
        mock_result = MagicMock(returncode=0, stderr="")

        def run():
            with patch("sys.argv", ["run_sv_tests.py", "--junit-xml", xml_path]), \
                 patch("run_sv_tests.check_binary"), \
                 patch("run_sv_tests.glob.glob", return_value=fake_paths), \
                 patch("run_sv_tests.subprocess.run", return_value=mock_result):
                run_sv_tests.main()

        get_exit_code(run)
        assert Path(xml_path).exists()
