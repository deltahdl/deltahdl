"""Integration tests for run_sv_tests module."""

import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest


def _execute_one_test(
    rst: ModuleType, path: str, run: MagicMock,
) -> tuple[dict[str, object], int]:
    """Run execute_single_test() over path with run standing in for the tool.

    parse_metadata is patched to answer nothing, so the file's own comment
    stays out of the case and the result comes from the run alone.
    """
    with patch.object(rst.subprocess, "run", run), \
         patch.object(rst, "parse_metadata", return_value={}):
        outcome: tuple[dict[str, object], int] = rst.execute_single_test(path)
    return outcome


def _execute_one_passing_test(rst: ModuleType) -> tuple[dict[str, object], int]:
    """Run execute_single_test() over a file the tool accepts."""
    return _execute_one_test(
        rst, "/tests/chapter-5/foo.sv",
        MagicMock(return_value=MagicMock(returncode=0, stderr="")),
    )


def _execute_one_timing_out_test(rst: ModuleType) -> tuple[dict[str, object], int]:
    """Run execute_single_test() over a file the tool never finishes with."""
    return _execute_one_test(
        rst, "/tests/chapter-5/bar.sv",
        MagicMock(side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30)),
    )


class TestExecuteSingleTest:
    """Tests for execute_single_test() wiring run_test to print_result."""

    def test_returns_dict_with_all_required_keys(self, rst: ModuleType) -> None:
        """execute_single_test() should return a dict with all required keys."""
        result, _ = _execute_one_passing_test(rst)
        assert set(result) == {
            "name", "chapter", "status", "time", "stderr", "should_fail",
            "returncode", "clause",
        }

    def test_reports_the_file_it_ran_and_what_the_run_said(
        self, rst: ModuleType,
    ) -> None:
        """execute_single_test() should name the file, its chapter and the outcome."""
        result, _ = _execute_one_passing_test(rst)
        assert {k: result[k] for k in ("name", "chapter", "status", "stderr")} == {
            "name": "foo.sv", "chapter": "chapter-5",
            "status": "pass", "stderr": "",
        }

    def test_an_accepted_file_scores_a_pass(self, rst: ModuleType) -> None:
        """execute_single_test() should count a file the tool accepted as one pass."""
        assert _execute_one_passing_test(rst)[1] == 1

    def test_prints_pass_for_an_accepted_file(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """execute_single_test() should print PASS for a file the tool accepted."""
        _execute_one_passing_test(rst)
        assert "PASS" in capsys.readouterr().out

    def test_timeout_produces_timeout_status(self, rst: ModuleType) -> None:
        """execute_single_test() should catch TimeoutExpired and set status."""
        result, _ = _execute_one_timing_out_test(rst)
        assert result["status"] == "timeout"

    def test_timeout_names_the_file_that_did_not_finish(
        self, rst: ModuleType,
    ) -> None:
        """execute_single_test() should name the file in a timed-out result."""
        result, _ = _execute_one_timing_out_test(rst)
        assert result["name"] == "bar.sv"

    def test_timeout_scores_no_pass(self, rst: ModuleType) -> None:
        """execute_single_test() should count a timed-out file as no pass."""
        assert _execute_one_timing_out_test(rst)[1] == 0

    def test_prints_timeout_for_a_file_that_did_not_finish(
        self, rst: ModuleType, capsys: pytest.CaptureFixture[str],
    ) -> None:
        """execute_single_test() should print TIMEOUT for a timed-out file."""
        _execute_one_timing_out_test(rst)
        assert "TIMEOUT" in capsys.readouterr().out


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

    assert [(r["name"], r["chapter"]) for r in results] == [
        ("a.sv", "chapter-5"), ("b.sv", "chapter-6"),
    ]


def test_pipeline_carries_the_diagnostic_of_an_expected_rejection(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """A file meant to be rejected is reported with what the tool said about it.

    Such a file passes by being rejected, so the metadata that inverts the
    outcome and the message that justifies it have to arrive at the printing
    together for the run to be readable.
    """
    mock_result = MagicMock(returncode=1, stderr="a.sv:3:1: error: redeclared")

    with patch.object(rst.glob, "glob", return_value=["/tests/chapter-5/a.sv"]), \
         patch.object(rst.subprocess, "run", return_value=mock_result), \
         patch.object(
             rst, "parse_metadata",
             return_value={"should_fail_because": "Variable redeclaration"},
         ):
        for path in rst.collect_tests():
            rst.execute_single_test(path)

    assert "a.sv:3:1: error: redeclared" in capsys.readouterr().out


def _junit_root_over_one_pass_and_one_failure(
    rst: ModuleType, tmp_path: Path,
) -> ET.Element:
    """Write a report for one passing and one failing file and parse it back."""
    results = [
        {"name": "x.sv", "chapter": "chapter-5", "status": "pass",
         "time": 0.5, "stderr": ""},
        {"name": "y.sv", "chapter": "chapter-5", "status": "fail",
         "time": 0.3, "stderr": "lint error"},
    ]
    filepath = str(tmp_path / "results.xml")
    rst.write_junit_xml(results, 1.0, filepath)
    return ET.parse(filepath).getroot()


def test_write_junit_xml_names_the_suite(
    rst: ModuleType, tmp_path: Path,
) -> None:
    """write_junit_xml() should write a testsuite element named sv-tests."""
    root = _junit_root_over_one_pass_and_one_failure(rst, tmp_path)
    assert (root.tag, root.attrib["name"]) == ("testsuite", "sv-tests")


def test_write_junit_xml_writes_a_testcase_for_each_result(
    rst: ModuleType, tmp_path: Path,
) -> None:
    """write_junit_xml() should write one testcase per result, in order."""
    root = _junit_root_over_one_pass_and_one_failure(rst, tmp_path)
    assert [tc.attrib["name"] for tc in root.findall("testcase")] == [
        "x.sv", "y.sv",
    ]


def test_write_junit_xml_carries_the_failure_text(
    rst: ModuleType, tmp_path: Path,
) -> None:
    """write_junit_xml() should give a failing testcase what the tool said."""
    root = _junit_root_over_one_pass_and_one_failure(rst, tmp_path)
    fail_tc = [
        tc for tc in root.findall("testcase") if tc.attrib["name"] == "y.sv"
    ][0]
    assert [f.text for f in fail_tc.findall("failure")] == ["lint error"]


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


def _all_passing_run(rst: ModuleType) -> Callable[[], None]:
    """Return a callable running main() over one file the tool accepts."""
    def run() -> None:
        _run_main_patched(
            rst, ["/tests/chapter-5/a.sv"],
            MagicMock(returncode=0, stderr=""),
        )
    return run


def _run_with_a_failing_pool(rst: ModuleType) -> Callable[[], None]:
    """Return a callable running main() where ThreadPoolExecutor.map raises."""
    def run() -> None:
        with patch("sys.argv", ["run_sv_tests.py"]), \
             patch.object(rst, "check_binary"), \
             patch.object(rst.glob, "glob", return_value=["/tests/chapter-5/a.sv"]), \
             patch.object(rst, "ThreadPoolExecutor") as mock_pool_cls:
            mock_pool_cls.return_value.__enter__.return_value \
                .map.side_effect = OSError("too many open files")
            rst.main()
    return run


class TestMain:
    """Tests for the main() function."""

    def test_all_pass_exits_zero(
        self,
        rst: ModuleType,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() exits 0 when every file the run collected passed."""
        assert get_exit_code(_all_passing_run(rst)) == 0

    def test_all_pass_summary_gives_the_percentage(
        self,
        rst: ModuleType,
        capsys: pytest.CaptureFixture[str],
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main()'s summary reports the share of files that passed."""
        get_exit_code(_all_passing_run(rst))
        assert "100.0%" in capsys.readouterr().out

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

    def test_pool_map_exception_still_exits(
        self,
        rst: ModuleType,
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() exits 0 rather than raising when pool.map raises."""
        assert get_exit_code(_run_with_a_failing_pool(rst)) == 0

    def test_pool_map_exception_prints_a_diagnostic(
        self,
        rst: ModuleType,
        capsys: pytest.CaptureFixture[str],
        get_exit_code: Callable[[Callable[[], object]], int | str | None],
    ) -> None:
        """main() reports how far the run got when pool.map raises."""
        get_exit_code(_run_with_a_failing_pool(rst))
        assert "pool.map failed after 0/1" in capsys.readouterr().err

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
