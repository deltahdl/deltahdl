import subprocess
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch
from xml.etree import ElementTree as ET

import pytest


def _execute_one_test(rst: ModuleType, path: str, run: MagicMock) -> tuple[dict[str, object], int]:
    with patch.object(rst.subprocess, "run", run), \
         patch.object(rst, "parse_metadata", return_value={}):
        result, ok_int = rst.build_result(path)
        rst.print_status(result, ok_int)
    return result, ok_int


def _execute_one_passing_test(rst: ModuleType) -> tuple[dict[str, object], int]:
    return _execute_one_test(
        rst, "/tests/chapter-5/foo.sv",
        MagicMock(return_value=MagicMock(returncode=0, stderr="")),
    )


def _execute_one_timing_out_test(rst: ModuleType) -> tuple[dict[str, object], int]:
    return _execute_one_test(
        rst, "/tests/chapter-5/bar.sv",
        MagicMock(side_effect=subprocess.TimeoutExpired(cmd="x", timeout=30)),
    )


def test_returns_dict_with_all_required_keys(rst: ModuleType) -> None:
    result, _ = _execute_one_passing_test(rst)
    assert set(result) == {
        "name", "chapter", "status", "time", "stderr", "should_fail",
        "returncode", "clause",
    }


def test_reports_the_file_it_ran_and_what_the_run_said(rst: ModuleType) -> None:
    result, _ = _execute_one_passing_test(rst)
    assert {k: result[k] for k in ("name", "chapter", "status", "stderr")} == {
        "name": "foo.sv", "chapter": "chapter-5",
        "status": "pass", "stderr": "",
    }


def test_an_accepted_file_evaluates_as_a_pass(rst: ModuleType) -> None:
    assert _execute_one_passing_test(rst)[1] == 1


def test_prints_pass_for_an_accepted_file(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _execute_one_passing_test(rst)
    assert "PASS" in capsys.readouterr().out


def test_timeout_produces_timeout_status(rst: ModuleType) -> None:
    result, _ = _execute_one_timing_out_test(rst)
    assert result["status"] == "timeout"


def test_timeout_names_the_file_that_did_not_finish(rst: ModuleType) -> None:
    result, _ = _execute_one_timing_out_test(rst)
    assert result["name"] == "bar.sv"


def test_timeout_does_not_evaluate_as_a_pass(rst: ModuleType) -> None:
    assert _execute_one_timing_out_test(rst)[1] == 0


def test_prints_timeout_for_a_file_that_did_not_finish(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _execute_one_timing_out_test(rst)
    assert "TIMEOUT" in capsys.readouterr().out


def test_pipeline_produces_correct_result_list(rst: ModuleType) -> None:
    fake_paths = ["/tests/chapter-5/a.sv", "/tests/chapter-6/b.sv"]
    mock_result = MagicMock(returncode=0, stderr="")

    with patch.object(rst.glob, "glob", return_value=fake_paths), \
         patch.object(rst.subprocess, "run", return_value=mock_result), \
         patch.object(rst, "parse_metadata", return_value={}):
        tests = rst.collect_tests()
        results = []
        for path in tests:
            result, _ = rst.build_result(path)
            results.append(result)

    assert [(r["name"], r["chapter"]) for r in results] == [
        ("a.sv", "chapter-5"), ("b.sv", "chapter-6"),
    ]


def test_pipeline_carries_the_diagnostic_of_an_expected_rejection(
    rst: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    mock_result = MagicMock(returncode=1, stderr="a.sv:3:1: error: redeclared")

    with patch.object(rst.glob, "glob", return_value=["/tests/chapter-5/a.sv"]), \
         patch.object(rst.subprocess, "run", return_value=mock_result), \
         patch.object(
             rst, "parse_metadata",
             return_value={"should_fail_because": "Variable redeclaration"},
         ):
        for path in rst.collect_tests():
            rst.print_status(*rst.build_result(path))

    assert "a.sv:3:1: error: redeclared" in capsys.readouterr().out


def _junit_root_over_one_pass_and_one_failure(rst: ModuleType, tmp_path: Path) -> ET.Element:
    results = [
        {"name": "x.sv", "chapter": "chapter-5", "status": "pass",
         "time": 0.5, "stderr": ""},
        {"name": "y.sv", "chapter": "chapter-5", "status": "fail",
         "time": 0.3, "stderr": "lint error"},
    ]
    filepath = str(tmp_path / "results.xml")
    rst.write_junit_xml(results, 1.0, filepath)
    return ET.parse(filepath).getroot()


def test_write_junit_xml_names_the_suite(rst: ModuleType, tmp_path: Path) -> None:
    root = _junit_root_over_one_pass_and_one_failure(rst, tmp_path)
    assert (root.tag, root.attrib["name"]) == ("testsuite", "sv-tests")


def test_write_junit_xml_writes_a_testcase_for_each_result(rst: ModuleType, tmp_path: Path) -> None:
    root = _junit_root_over_one_pass_and_one_failure(rst, tmp_path)
    assert [tc.attrib["name"] for tc in root.findall("testcase")] == [
        "x.sv", "y.sv",
    ]


def test_write_junit_xml_carries_the_failure_text(rst: ModuleType, tmp_path: Path) -> None:
    root = _junit_root_over_one_pass_and_one_failure(rst, tmp_path)
    fail_tc = [
        tc for tc in root.findall("testcase") if tc.attrib["name"] == "y.sv"
    ][0]
    assert [f.text for f in fail_tc.findall("failure")] == ["lint error"]


def test_junit_xml_flag(rst: ModuleType) -> None:
    with patch("sys.argv", ["run_sv_tests.py", "--junit-xml", "out.xml"]):
        args = rst.parse_args()
    assert args.junit_xml == "out.xml"


def test_no_flags_defaults_to_none(rst: ModuleType) -> None:
    with patch("sys.argv", ["run_sv_tests.py"]):
        args = rst.parse_args()
    assert args.junit_xml is None


def _run_main_patched(
    rst: ModuleType,
    fake_paths: list[str],
    mock_result: MagicMock,
    extra_argv: list[str] | None = None,
) -> None:
    argv = ["run_sv_tests.py"] + (extra_argv or [])
    with patch("sys.argv", argv), \
         patch.object(rst, "check_binary"), \
         patch.object(rst.glob, "glob", return_value=fake_paths), \
         patch.object(rst.subprocess, "run", return_value=mock_result), \
         patch.object(rst, "load_libraries", return_value={}), \
         patch.object(rst, "parse_metadata", return_value={}):
        rst.main()


def _all_passing_run(rst: ModuleType) -> Callable[[], None]:
    def run() -> None:
        _run_main_patched(
            rst, ["/tests/chapter-5/a.sv"],
            MagicMock(returncode=0, stderr=""),
        )
    return run


def _main_over_one_file(rst: ModuleType, **patches: Any) -> Callable[[], None]:
    def run() -> None:
        with patch("sys.argv", ["run_sv_tests.py"]), \
             patch.object(rst, "check_binary"), \
             patch.object(rst.glob, "glob", return_value=["/tests/chapter-5/a.sv"]), \
             patch.multiple(rst, **patches):
            rst.main()
    return run


def _run_with_a_failing_pool(rst: ModuleType) -> Callable[[], None]:
    mock_pool_cls = MagicMock()
    mock_pool_cls.return_value.__enter__.return_value \
        .map.side_effect = OSError("too many open files")
    return _main_over_one_file(
        rst, load_libraries=MagicMock(return_value={}),
        ThreadPoolExecutor=mock_pool_cls,
    )


def _pool_mapping_as_consumed() -> MagicMock:
    mock_pool_cls = MagicMock()
    mock_pool_cls.return_value.__enter__.return_value \
        .map.side_effect = map
    return mock_pool_cls


def _events_of_a_run_over_two_files(rst: ModuleType) -> list[str]:
    events: list[str] = []

    def build(path: str, libraries: object = None) -> tuple[dict[str, Any], int]:
        del libraries
        events.append(f"build {Path(path).name}")
        return {
            "name": Path(path).name, "chapter": "chapter-5",
            "status": "pass", "time": 0.0, "stderr": "",
        }, 1

    def show(result: dict[str, Any], ok: int) -> None:
        del ok
        events.append(f"print {result['name']}")

    with patch("sys.argv", ["run_sv_tests.py"]), \
         patch.object(rst, "check_binary"), \
         patch.object(
             rst.glob, "glob",
             return_value=["/tests/chapter-5/a.sv", "/tests/chapter-5/b.sv"],
         ), \
         patch.object(rst, "load_libraries", return_value={}), \
         patch.object(rst, "build_result", build), \
         patch.object(rst, "print_status", show), \
         patch.object(rst, "ThreadPoolExecutor", _pool_mapping_as_consumed()), \
         pytest.raises(SystemExit):
        rst.main()
    return events


def test_prints_each_result_before_the_next_file_is_built(rst: ModuleType) -> None:
    assert _events_of_a_run_over_two_files(rst) == [
        "build a.sv", "print a.sv", "build b.sv", "print b.sv",
    ]


def test_all_pass_exits_zero(
    rst: ModuleType,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    assert get_exit_code(_all_passing_run(rst)) == 0


def test_all_pass_summary_gives_the_percentage(
    rst: ModuleType,
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    get_exit_code(_all_passing_run(rst))
    assert "100.0%" in capsys.readouterr().out


def test_no_tests_exits_one(
    rst: ModuleType,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    def run() -> None:
        with patch("sys.argv", ["run_sv_tests.py"]), \
             patch.object(rst, "check_binary"), \
             patch.object(rst.glob, "glob", return_value=[]):
            rst.main()

    assert get_exit_code(run) == 1


def _run_with_a_library_not_checked_out(
    rst: ModuleType, mock_pool_cls: MagicMock | None = None,
) -> Callable[[], None]:
    return _main_over_one_file(
        rst,
        load_libraries=MagicMock(side_effect=FileNotFoundError(
            "library 'uvm' names /tp/uvm_pkg.sv, which is not checked out",
        )),
        ThreadPoolExecutor=mock_pool_cls or MagicMock(),
    )


def test_a_library_not_checked_out_exits_one(
    rst: ModuleType,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    assert get_exit_code(_run_with_a_library_not_checked_out(rst)) == 1


def test_a_library_not_checked_out_is_named_on_stderr(
    rst: ModuleType,
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    get_exit_code(_run_with_a_library_not_checked_out(rst))
    assert (
        "error: FileNotFoundError: library 'uvm' names /tp/uvm_pkg.sv"
        in capsys.readouterr().err
    )


def test_a_library_not_checked_out_stops_the_run_before_any_file(
    rst: ModuleType,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    mock_pool_cls = MagicMock()
    get_exit_code(_run_with_a_library_not_checked_out(rst, mock_pool_cls))
    assert mock_pool_cls.call_count == 0


def test_pool_map_exception_still_exits(
    rst: ModuleType,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    assert get_exit_code(_run_with_a_failing_pool(rst)) == 0


def test_pool_map_exception_prints_a_diagnostic(
    rst: ModuleType,
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
    get_exit_code(_run_with_a_failing_pool(rst))
    assert "pool.map failed after 0/1" in capsys.readouterr().err


def test_writes_junit_xml(
    rst: ModuleType,
    tmp_path: Path,
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
) -> None:
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
