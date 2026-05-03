"""Integration tests for run_sv_tests module."""

import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest


class TestExecuteSingleTest:
    """Tests for execute_single_test() wiring run_test to print_result."""

    def test_returns_dict_with_all_required_keys(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """execute_single_test() should return a dict with all required keys."""
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(rst.subprocess, "run", return_value=mock_result), \
             patch.object(rst, "parse_metadata", return_value={}):
            result, ok = rst.execute_single_test(
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

    def test_timeout_produces_timeout_status(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """execute_single_test() should catch TimeoutExpired and set status."""
        with patch.object(
            rst.subprocess, "run",
            side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30),
        ), patch.object(rst, "parse_metadata", return_value={}):
            result, ok = rst.execute_single_test(
                "/tests/chapter-5/bar.sv"
            )
        captured = capsys.readouterr().out
        assert (
            ok == 0
            and result["status"] == "timeout"
            and result["name"] == "bar.sv"
            and "TIMEOUT" in captured
        )


def test_pipeline_produces_correct_result_list(rst: ModuleType) -> None:
    """Collecting tests and executing them yields correct result dicts."""
    fake_paths = ["/tests/chapter-5/a.sv", "/tests/chapter-6/b.sv"]
    mock_result = MagicMock(returncode=0, stderr="")

    with patch.object(rst.glob, "glob", return_value=fake_paths), \
         patch.object(rst.subprocess, "run", return_value=mock_result), \
         patch.object(rst, "parse_metadata", return_value={}):
        tests = rst.collect_tests()
        results = []
        for path in tests:
            result, _ = rst.execute_single_test(path)
            results.append(result)

    assert (
        len(results) == 2
        and results[0]["name"] == "a.sv"
        and results[0]["chapter"] == "chapter-5"
        and results[1]["name"] == "b.sv"
        and results[1]["chapter"] == "chapter-6"
    )


def test_write_junit_xml_round_trip_preserves_structure(
    rst: ModuleType, tmp_path: Path,
) -> None:
    """Write XML, parse it back, verify full structure."""
    results = [
        {"name": "x.sv", "chapter": "chapter-5", "status": "pass",
         "time": 0.5, "stderr": ""},
        {"name": "y.sv", "chapter": "chapter-5", "status": "fail",
         "time": 0.3, "stderr": "lint error"},
    ]
    filepath = str(tmp_path / "results.xml")
    rst.write_junit_xml(results, 1.0, filepath)

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

    def test_junit_xml_flag(self, rst: ModuleType) -> None:
        """parse_args() should set junit_xml when --junit-xml is given."""
        with patch("sys.argv", ["run_sv_tests.py", "--junit-xml", "out.xml"]):
            args = rst.parse_args()
        assert args.junit_xml == "out.xml"

    def test_no_flags_defaults_to_none(self, rst: ModuleType) -> None:
        """parse_args() with no flags should leave junit_xml as None."""
        with patch("sys.argv", ["run_sv_tests.py"]):
            args = rst.parse_args()
        assert args.junit_xml is None


def _run_main_patched(
    rst: ModuleType,
    fake_paths: list[str],
    mock_result: MagicMock,
    extra_argv: list[str] | None = None,
) -> None:
    """Run rst.main() with standard patches for check_binary/glob/subprocess/metadata."""
    argv = ["run_sv_tests.py"] + (extra_argv or [])
    with patch("sys.argv", argv), \
         patch.object(rst, "check_binary"), \
         patch.object(rst.glob, "glob", return_value=fake_paths), \
         patch.object(rst.subprocess, "run", return_value=mock_result), \
         patch.object(rst, "parse_metadata", return_value={}):
        rst.main()


class TestMain:
    """Tests for the main() function."""

    def test_all_pass_exits_zero_with_percentage(
        self,
        rst: ModuleType,
        capsys: pytest.CaptureFixture[str],
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() exits 0 and summary includes pass percentage."""
        fake_paths = ["/tests/chapter-5/a.sv"]
        mock_result = MagicMock(returncode=0, stderr="")

        def run() -> None:
            _run_main_patched(rst, fake_paths, mock_result)

        assert get_exit_code(run) == 0 and "100.0%" in capsys.readouterr().out

    def test_no_tests_exits_one(
        self,
        rst: ModuleType,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() exits 1 when no .sv files are found."""

        def run() -> None:
            with patch("sys.argv", ["run_sv_tests.py"]), \
                 patch.object(rst, "check_binary"), \
                 patch.object(rst.glob, "glob", return_value=[]):
                rst.main()

        assert get_exit_code(run) == 1

    def test_pool_map_exception_prints_error_and_continues(
        self,
        rst: ModuleType,
        capsys: pytest.CaptureFixture[str],
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() prints diagnostic and still exits when pool.map raises."""
        fake_paths = ["/tests/chapter-5/a.sv"]

        def run() -> None:
            with patch("sys.argv", ["run_sv_tests.py"]), \
                 patch.object(rst, "check_binary"), \
                 patch.object(rst.glob, "glob", return_value=fake_paths), \
                 patch.object(rst, "ThreadPoolExecutor") as mock_pool_cls:
                mock_pool_cls.return_value.__enter__.return_value \
                    .map.side_effect = OSError("too many open files")
                rst.main()

        assert (
            get_exit_code(run) == 0
            and "pool.map failed after 0/1" in capsys.readouterr().err
        )

    def test_writes_junit_xml(
        self,
        rst: ModuleType,
        tmp_path: Path,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() writes JUnit XML when --junit-xml is given."""
        xml_path = str(tmp_path / "report.xml")
        fake_paths = ["/tests/chapter-5/a.sv"]
        mock_result = MagicMock(returncode=0, stderr="")

        def run() -> None:
            _run_main_patched(
                rst, fake_paths, mock_result,
                extra_argv=["--junit-xml", xml_path],
            )

        get_exit_code(run)
        assert Path(xml_path).exists()
