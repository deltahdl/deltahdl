"""Unit tests for the classify_files module."""

import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import classify_files
from helpers import (
    stub_fetch_issue_title,
    stub_subprocess_failure,
    stub_subprocess_success,
    stub_tick_file_checkbox,
)

_parse_args = getattr(classify_files, "_parse_args")
_build_command = getattr(classify_files, "_build_command")
_run = getattr(classify_files, "_run")
extract_filename_from_title = getattr(
    classify_files, "extract_filename_from_title",
)
resolve_sub_issues = getattr(classify_files, "resolve_sub_issues")


# ---- Helpers ---------------------------------------------------------------


_BASE_ARGV = [
    "prog",
    "--files", "a.cpp,b.cpp",
    "--issue", "61",
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
    "--organization", "testorg",
    "--repo", "testrepo",
    "--max-lines", "1000",
]

_SUB_ISSUES_ARGV = [
    "prog",
    "--sub-issues", "76,77",
    "--issue", "61",
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
    "--organization", "testorg",
    "--repo", "testrepo",
    "--max-lines", "1000",
]


def _make_args(**overrides):
    """Build a SimpleNamespace with all required args."""
    defaults = {
        "files": "a.cpp,b.cpp",
        "sub_issues": None,
        "issue": 61,
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "organization": "testorg",
        "repo": "testrepo",
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_files(monkeypatch):
    """Parses --files flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().files == "a.cpp,b.cpp"


def test_parse_args_issue(monkeypatch):
    """Parses --issue flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().issue == 61


def test_parse_args_issue_required(monkeypatch):
    """Rejects missing --issue."""
    argv = [a for a in _BASE_ARGV if a not in ("--issue", "61")]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_output_dir(monkeypatch):
    """Parses --output-dir flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().output_dir == "/out"


def test_parse_args_lrm(monkeypatch):
    """Parses --lrm flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().lrm == "/lrm.txt"


def test_parse_args_organization(monkeypatch):
    """Parses --organization flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().organization == "testorg"


def test_parse_args_organization_required(monkeypatch):
    """Rejects missing --organization."""
    argv = [a for a in _BASE_ARGV
            if a not in ("--organization", "testorg")]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_repo(monkeypatch):
    """Parses --repo flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().repo == "testrepo"


def test_parse_args_repo_required(monkeypatch):
    """Rejects missing --repo."""
    argv = [a for a in _BASE_ARGV
            if a not in ("--repo", "testrepo")]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_max_lines(monkeypatch):
    """Parses --max-lines flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().max_lines == 1000


def test_parse_args_max_lines_required(monkeypatch):
    """Rejects missing --max-lines."""
    argv = [a for a in _BASE_ARGV
            if a not in ("--max-lines", "1000")]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_prog_name(monkeypatch, capsys):
    """Usage line shows classify_files as program name."""
    monkeypatch.setattr(sys, "argv", ["prog", "--help"])
    try:
        _parse_args()
    except SystemExit:
        pass
    assert "classify_files" in capsys.readouterr().out


# ---- _build_command --------------------------------------------------------


def test_build_command_invokes_classify_file():
    """Command starts with python -m classify_file."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[:3] == [sys.executable, "-m", "classify_file"]


def test_build_command_file_flag():
    """Command contains --file with the given path."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[cmd.index("--file") + 1] == "/path/a.cpp"


def test_build_command_create_issue_flag():
    """Command contains --create-issue."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert "--create-issue" in cmd


def test_build_command_no_issue_number():
    """Command does not contain --issue."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert "--issue" not in cmd


def test_build_command_output_dir_flag():
    """Command contains correct --output-dir value."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag():
    """Command contains correct --lrm value."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_organization_flag():
    """Command contains correct --organization value."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[cmd.index("--organization") + 1] == "testorg"


def test_build_command_repo_flag():
    """Command contains correct --repo value."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[cmd.index("--repo") + 1] == "testrepo"


def test_build_command_max_lines_flag():
    """Command contains correct --max-lines value."""
    cmd = _build_command(_make_args(), "/path/a.cpp")
    assert cmd[cmd.index("--max-lines") + 1] == "1000"


# ---- run_classify_file -----------------------------------------------------


def test_run_classify_file_succeeds_silently(monkeypatch):
    """No SystemExit when subprocess succeeds."""
    captured = stub_subprocess_success(monkeypatch)
    classify_files.run_classify_file(_make_args(), "/p/a.cpp", 1, 1)
    assert len(captured) == 1


def test_run_classify_file_exits_on_failure(monkeypatch):
    """SystemExit when subprocess fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        classify_files.run_classify_file(
            _make_args(), "/p/a.cpp", 1, 1,
        )


def test_run_classify_file_prints_progress(
    monkeypatch, capsys,
):
    """Prints progress line with file index and name."""
    stub_subprocess_success(monkeypatch)
    classify_files.run_classify_file(
        _make_args(), "/p/b.cpp", 2, 5,
    )
    assert "Processing file 2/5: b.cpp" in capsys.readouterr().out


def test_run_classify_file_passes_file_path(monkeypatch):
    """Subprocess command contains the correct --file value."""
    captured = stub_subprocess_success(monkeypatch)
    classify_files.run_classify_file(
        _make_args(), "/p/a.cpp", 1, 1,
    )
    assert captured[0][captured[0].index("--file") + 1] == "/p/a.cpp"


def test_run_classify_file_forwards_stdout(monkeypatch, capsys):
    """Subprocess stdout appears in parent stdout."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "child output\n"
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda _cmd, **_kw: mock_result,
    )
    classify_files.run_classify_file(
        _make_args(), "/p/a.cpp", 1, 1,
    )
    assert "child output" in capsys.readouterr().out


def test_run_classify_file_prints_stderr_on_failure(
    monkeypatch, capsys,
):
    """Subprocess stderr appears in parent stderr on failure."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error details\n"
    monkeypatch.setattr(
        subprocess, "run", lambda _cmd, **_kw: mock_result,
    )
    try:
        classify_files.run_classify_file(
            _make_args(), "/p/a.cpp", 1, 1,
        )
    except SystemExit:
        pass
    assert "error details" in capsys.readouterr().err


# ---- tick_file_checkbox ----------------------------------------------------


def test_tick_file_checkbox_calls_fetch(monkeypatch):
    """Fetches the issue body with correct arguments."""
    calls: list[tuple] = []
    monkeypatch.setattr(
        classify_files, "fetch_issue_body",
        lambda org, repo, issue: (
            calls.append((org, repo, issue))
            or "- [ ] a.cpp\n"
        ),
    )
    monkeypatch.setattr(
        classify_files, "tick_checkbox",
        lambda body, _name: body,
    )
    monkeypatch.setattr(
        classify_files, "update_issue_body",
        lambda _o, _r, _i, _b: None,
    )
    classify_files.tick_file_checkbox("myorg", "myrepo", 61, "a.cpp")
    assert calls[0] == ("myorg", "myrepo", 61)


def test_tick_file_checkbox_calls_tick(monkeypatch):
    """Ticks the checkbox for the given filename."""
    ticked: list[str] = []
    monkeypatch.setattr(
        classify_files, "fetch_issue_body",
        lambda _o, _r, _i: "- [ ] a.cpp\n",
    )
    monkeypatch.setattr(
        classify_files, "tick_checkbox",
        lambda body, name: (ticked.append(name) or body),
    )
    monkeypatch.setattr(
        classify_files, "update_issue_body",
        lambda _o, _r, _i, _b: None,
    )
    classify_files.tick_file_checkbox("o", "r", 1, "a.cpp")
    assert ticked[0] == "a.cpp"


def test_tick_file_checkbox_calls_update(monkeypatch):
    """Updates the issue body after ticking."""
    updated: list[str] = []
    monkeypatch.setattr(
        classify_files, "fetch_issue_body",
        lambda _o, _r, _i: "- [ ] a.cpp\n",
    )
    monkeypatch.setattr(
        classify_files, "tick_checkbox",
        lambda _body, _name: "- [x] a.cpp\n",
    )
    monkeypatch.setattr(
        classify_files, "update_issue_body",
        lambda _o, _r, _i, body: updated.append(body),
    )
    classify_files.tick_file_checkbox("o", "r", 1, "a.cpp")
    assert updated[0] == "- [x] a.cpp\n"


# ---- _run ------------------------------------------------------------------


def test_run_processes_all_files(monkeypatch):
    """Subprocess invoked once per file."""
    captured = stub_subprocess_success(monkeypatch)
    stub_tick_file_checkbox(monkeypatch)
    _run(_make_args(files="a.cpp,b.cpp"))
    assert len(captured) == 2


def test_run_ticks_checkbox_after_each_file(monkeypatch):
    """Ticks file checkbox after each successful file."""
    stub_subprocess_success(monkeypatch)
    ticked = stub_tick_file_checkbox(monkeypatch)
    _run(_make_args(files="a.cpp,b.cpp"))
    assert ticked == ["a.cpp", "b.cpp"]


def test_run_splits_comma_separated_files(monkeypatch):
    """Comma-separated files result in distinct subprocess calls."""
    captured = stub_subprocess_success(monkeypatch)
    stub_tick_file_checkbox(monkeypatch)
    _run(_make_args(files="x.cpp,y.cpp"))
    files = [c[c.index("--file") + 1] for c in captured]
    assert files == ["x.cpp", "y.cpp"]


def test_run_prints_done(monkeypatch, capsys):
    """Prints Done after all files processed."""
    stub_subprocess_success(monkeypatch)
    stub_tick_file_checkbox(monkeypatch)
    _run(_make_args(files="a.cpp"))
    assert "Done" in capsys.readouterr().out


# ---- --sub-issues argument parsing -----------------------------------------


def test_parse_args_sub_issues(monkeypatch):
    """Parses --sub-issues flag."""
    monkeypatch.setattr(sys, "argv", _SUB_ISSUES_ARGV)
    assert _parse_args().sub_issues == "76,77"


def test_parse_args_files_and_sub_issues_rejects(monkeypatch):
    """Both --files and --sub-issues are rejected."""
    monkeypatch.setattr(sys, "argv", [
        "prog",
        "--files", "a.cpp",
        "--sub-issues", "76",
        "--issue", "61",
        "--output-dir", "/out",
        "--lrm", "/lrm.txt",
        "--organization", "testorg",
        "--repo", "testrepo",
        "--max-lines", "1000",
    ])
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_neither_rejects(monkeypatch):
    """Neither --files nor --sub-issues is rejected."""
    monkeypatch.setattr(sys, "argv", [
        "prog",
        "--issue", "61",
        "--output-dir", "/out",
        "--lrm", "/lrm.txt",
        "--organization", "testorg",
        "--repo", "testrepo",
        "--max-lines", "1000",
    ])
    with pytest.raises(SystemExit):
        _parse_args()


# ---- fetch_issue_title -----------------------------------------------------


def test_fetch_issue_title_returns_title(monkeypatch):
    """Returns stripped stdout from gh api."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "Classify tests in foo.cpp\n"
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda _cmd, **_kw: mock_result,
    )
    assert classify_files.fetch_issue_title("o", "r", 1) == (
        "Classify tests in foo.cpp"
    )


def test_fetch_issue_title_exits_on_failure(monkeypatch):
    """sys.exit(1) when gh api fails."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "not found"
    monkeypatch.setattr(
        subprocess, "run", lambda _cmd, **_kw: mock_result,
    )
    with pytest.raises(SystemExit):
        classify_files.fetch_issue_title("o", "r", 999)


# ---- extract_filename_from_title ------------------------------------------


def test_extract_filename_from_title_valid():
    """Extracts filename from valid title."""
    assert extract_filename_from_title(
        "Classify tests in foo.cpp",
    ) == "foo.cpp"


def test_extract_filename_from_title_invalid():
    """sys.exit(1) on non-matching title."""
    with pytest.raises(SystemExit):
        extract_filename_from_title("Unrelated title")


# ---- resolve_sub_issues ---------------------------------------------------


def test_resolve_sub_issues_returns_entries(monkeypatch):
    """Maps issue numbers to (path, issue) pairs."""
    stub_fetch_issue_title(monkeypatch, {
        76: "Classify tests in a.cpp",
        77: "Classify tests in b.cpp",
    })
    args = _make_args(sub_issues="76,77")
    entries = resolve_sub_issues(args)
    assert entries == [("/out/a.cpp", 76), ("/out/b.cpp", 77)]


# ---- _build_command with sub_issue ----------------------------------------


def test_build_command_with_sub_issue():
    """sub_issue=76 produces --issue 76."""
    cmd = _build_command(_make_args(), "/p/a.cpp", sub_issue=76)
    assert cmd[cmd.index("--issue") + 1] == "76"


def test_build_command_with_sub_issue_no_create():
    """sub_issue=76 excludes --create-issue."""
    cmd = _build_command(_make_args(), "/p/a.cpp", sub_issue=76)
    assert "--create-issue" not in cmd


def test_build_command_without_sub_issue():
    """sub_issue=None keeps --create-issue (backward compat)."""
    cmd = _build_command(_make_args(), "/p/a.cpp")
    assert "--create-issue" in cmd


# ---- _run with --sub-issues -----------------------------------------------


def test_run_sub_issues_passes_issue_flag(monkeypatch):
    """_run with sub_issues passes --issue to each subprocess."""
    stub_fetch_issue_title(monkeypatch, {
        76: "Classify tests in a.cpp",
        77: "Classify tests in b.cpp",
    })
    captured = stub_subprocess_success(monkeypatch)
    stub_tick_file_checkbox(monkeypatch)
    _run(_make_args(files=None, sub_issues="76,77"))
    issues = [c[c.index("--issue") + 1] for c in captured]
    assert issues == ["76", "77"]


def test_run_sub_issues_ticks_master_checkbox(monkeypatch):
    """Master issue checkbox ticked after each file."""
    stub_fetch_issue_title(monkeypatch, {
        76: "Classify tests in a.cpp",
        77: "Classify tests in b.cpp",
    })
    stub_subprocess_success(monkeypatch)
    ticked = stub_tick_file_checkbox(monkeypatch)
    _run(_make_args(files=None, sub_issues="76,77"))
    assert ticked == ["a.cpp", "b.cpp"]


# ---- main ------------------------------------------------------------------


def test_main_calls_run(monkeypatch, capsys):
    """main() calls _run with parsed args."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    stub_subprocess_success(monkeypatch)
    stub_tick_file_checkbox(monkeypatch)
    classify_files.main()
    assert "Done" in capsys.readouterr().out
