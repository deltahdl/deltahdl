"""Unit tests for run-flow functions in classify_file."""

import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import classify_file

from helpers import (
    make_test_file,
    stub_close_issue,
    stub_create_issue,
    stub_ensure_unchecked,
    stub_subprocess_failure,
    stub_subprocess_mixed,
    stub_subprocess_success,
)

_parse_args = getattr(classify_file, "_parse_args")
_build_command = getattr(classify_file, "_build_command")
_run = getattr(classify_file, "_run")


# ---- Shared helpers --------------------------------------------------------


_BASE_ARGV = [
    "prog", "--file", "f.cpp",
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
    "--issue", "99",
    "--organization", "testorg",
    "--repo", "testrepo",
    "--max-lines", "1000",
]


def _make_args(**overrides):
    """Build a SimpleNamespace with all required args."""
    defaults = {
        "file": "/path/to/test.cpp",
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "issue": 99,
        "create_issue": False,
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def _make_run_args(tmp_path, **overrides):
    """Build args for _run with a real test file."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "lrm": str(tmp_path / "lrm.txt"),
        "issue": 99,
        "create_issue": False,
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_file(monkeypatch):
    """Parses --file flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().file == "f.cpp"


def test_parse_args_output_dir(monkeypatch):
    """Parses --output-dir flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().output_dir == "/out"


def test_parse_args_lrm(monkeypatch):
    """Parses --lrm flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().lrm == "/lrm.txt"


def test_parse_args_prog_name(monkeypatch, capsys):
    """Usage line shows 'classify_file' as program name."""
    monkeypatch.setattr(sys, "argv", ["prog", "--help"])
    try:
        _parse_args()
    except SystemExit:
        pass
    assert "classify_file" in capsys.readouterr().out


def test_parse_args_issue(monkeypatch):
    """Parses --issue as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--issue", "42"],
    )
    assert _parse_args().issue == 42


def test_parse_args_create_issue(monkeypatch):
    """Parses --create-issue flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue" and v != "--issue"]
    monkeypatch.setattr(
        sys, "argv", [*argv, "--create-issue"],
    )
    assert _parse_args().create_issue is True


def test_parse_args_create_issue_default_false(monkeypatch):
    """Defaults --create-issue to False when --issue is given."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().create_issue is False


def test_parse_args_neither_issue_flag_rejects(monkeypatch):
    """Rejects when neither --issue nor --create-issue is given."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue" and v != "--issue"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_both_issue_flags_reject(monkeypatch):
    """Rejects when both --issue and --create-issue are given."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--create-issue"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_organization(monkeypatch):
    """Parses --organization flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--organization", "myorg"],
    )
    assert _parse_args().organization == "myorg"


def test_parse_args_organization_required(monkeypatch):
    """Rejects missing --organization flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--organization"
            and v != "--organization"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_repo(monkeypatch):
    """Parses --repo flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--repo", "myrepo"],
    )
    assert _parse_args().repo == "myrepo"


def test_parse_args_repo_required(monkeypatch):
    """Rejects missing --repo flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--repo"
            and v != "--repo"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_dry_run(monkeypatch):
    """Parses --dry-run flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--dry-run"],
    )
    assert _parse_args().dry_run is True


def test_parse_args_dry_run_default(monkeypatch):
    """Defaults --dry-run to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().dry_run is False


def test_parse_args_no_commit(monkeypatch):
    """Parses --no-commit flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--no-commit"],
    )
    assert _parse_args().no_commit is True


def test_parse_args_no_commit_default(monkeypatch):
    """Defaults --no-commit to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().no_commit is False


def test_parse_args_max_lines(monkeypatch):
    """Parses --max-lines as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert _parse_args().max_lines == 500


def test_parse_args_max_lines_required(monkeypatch):
    """Rejects missing --max-lines flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--max-lines"
            and v != "--max-lines"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_no_test_flag(monkeypatch):
    """Rejects the --test flag since classify_file does not accept it."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--test", "T"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


# ---- _build_command --------------------------------------------------------


def test_build_command_basic():
    """Command starts with python -m classify_test."""
    cmd = _build_command(_make_args(), "T")
    assert cmd[:3] == [sys.executable, "-m", "classify_test"]


def test_build_command_file_flag():
    """Command includes --file with correct value."""
    cmd = _build_command(_make_args(file="/a/b.cpp"), "T")
    assert cmd[cmd.index("--file") + 1] == "/a/b.cpp"


def test_build_command_output_dir_flag():
    """Command includes --output-dir with correct value."""
    cmd = _build_command(_make_args(output_dir="/out"), "T")
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag():
    """Command includes --lrm with correct value."""
    cmd = _build_command(_make_args(lrm="/lrm.txt"), "T")
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_test_flag():
    """Command includes --test with the given test name."""
    cmd = _build_command(_make_args(), "FooBar")
    assert cmd[cmd.index("--test") + 1] == "FooBar"


def test_build_command_issue_included():
    """Command includes --issue with correct value."""
    cmd = _build_command(_make_args(issue=42), "T")
    assert cmd[cmd.index("--issue") + 1] == "42"


def test_build_command_organization_included():
    """Command includes --organization."""
    cmd = _build_command(_make_args(), "T")
    assert cmd[cmd.index("--organization") + 1] == "testorg"


def test_build_command_repo_included():
    """Command includes --repo."""
    cmd = _build_command(_make_args(), "T")
    assert cmd[cmd.index("--repo") + 1] == "testrepo"


def test_build_command_dry_run_included():
    """Command includes --dry-run when set."""
    cmd = _build_command(_make_args(dry_run=True), "T")
    assert "--dry-run" in cmd


def test_build_command_dry_run_omitted():
    """Command omits --dry-run when not set."""
    cmd = _build_command(_make_args(), "T")
    assert "--dry-run" not in cmd


def test_build_command_no_commit_included():
    """Command includes --no-commit when set."""
    cmd = _build_command(_make_args(no_commit=True), "T")
    assert "--no-commit" in cmd


def test_build_command_no_commit_omitted():
    """Command omits --no-commit when not set."""
    cmd = _build_command(_make_args(), "T")
    assert "--no-commit" not in cmd


def test_build_command_max_lines_included():
    """Command includes --max-lines."""
    cmd = _build_command(_make_args(), "T")
    assert cmd[cmd.index("--max-lines") + 1] == "1000"


def test_build_command_max_lines_value():
    """Command passes --max-lines with correct string value."""
    cmd = _build_command(_make_args(max_lines=500), "T")
    assert cmd[cmd.index("--max-lines") + 1] == "500"


# ---- run_classify_test -----------------------------------------------------


def test_run_classify_test_returns_true_on_success(monkeypatch):
    """Returns True when subprocess exits with 0."""
    stub_subprocess_success(monkeypatch)
    assert classify_file.run_classify_test(
        _make_args(), "T", 1, 1,
    ) is True


def test_run_classify_test_returns_false_on_failure(monkeypatch):
    """Returns False when subprocess exits with non-zero."""
    stub_subprocess_failure(monkeypatch)
    assert classify_file.run_classify_test(
        _make_args(), "T", 1, 1,
    ) is False


def test_run_classify_test_prints_progress(monkeypatch, capsys):
    """Prints progress line with index and name."""
    stub_subprocess_success(monkeypatch)
    classify_file.run_classify_test(_make_args(), "Alpha", 3, 10)
    assert "Processing test 3/10: Alpha" in capsys.readouterr().out


def test_run_classify_test_passes_test_name(monkeypatch):
    """Subprocess receives --test with the correct name."""
    captured = stub_subprocess_success(monkeypatch)
    classify_file.run_classify_test(_make_args(), "FooBar", 1, 1)
    assert captured[0][captured[0].index("--test") + 1] == "FooBar"


def test_run_classify_test_does_not_capture_output(monkeypatch):
    """Subprocess inherits stdout/stderr (no capture_output)."""
    kwargs_log: list[dict] = []

    def spy_run(_cmd, **kwargs):
        kwargs_log.append(kwargs)
        result = MagicMock()
        result.returncode = 0
        return result

    monkeypatch.setattr(subprocess, "run", spy_run)
    classify_file.run_classify_test(_make_args(), "T", 1, 1)
    assert "capture_output" not in kwargs_log[0]


# ---- build_issue_body ------------------------------------------------------


build_issue_body = classify_file.build_issue_body


def test_build_issue_body_summary_section():
    """Body contains the summary heading."""
    assert "## Summary" in build_issue_body("f.cpp", ["A"])


def test_build_issue_body_filename_in_path():
    """Body embeds filename in the test/src/unit path."""
    assert "test/src/unit/foo.cpp" in build_issue_body(
        "foo.cpp", ["A"],
    )


def test_build_issue_body_progress_line():
    """Body shows Progress: 0/N for N tests."""
    assert "Progress: 0/3" in build_issue_body(
        "f.cpp", ["A", "B", "C"],
    )


def test_build_issue_body_checkboxes():
    """Body contains unchecked checkboxes for each test name."""
    body = build_issue_body("f.cpp", ["Alpha", "Beta"])
    assert "- [ ] Alpha" in body


def test_build_issue_body_tests_header():
    """Body contains the Tests heading."""
    assert "## Tests" in build_issue_body("f.cpp", ["A"])


def test_build_issue_body_single_test():
    """Body works correctly with a single test."""
    assert "Progress: 0/1" in build_issue_body("f.cpp", ["Only"])


# ---- close_issue -----------------------------------------------------------


def test_close_issue_calls_gh_api(monkeypatch):
    """Invokes gh api with correct repo path and PATCH method."""
    captured = stub_subprocess_success(monkeypatch)
    classify_file.close_issue(_make_args(issue=42))
    assert "repos/testorg/testrepo/issues/42" in captured[0][2]


def test_close_issue_prints_confirmation(monkeypatch, capsys):
    """Prints confirmation message after closing."""
    stub_subprocess_success(monkeypatch)
    classify_file.close_issue(_make_args(issue=99))
    assert "Closed issue #99" in capsys.readouterr().out


def test_close_issue_exits_on_failure(monkeypatch):
    """Exits when gh api fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        classify_file.close_issue(_make_args())


# ---- create_issue ----------------------------------------------------------


def test_create_issue_calls_gh_api_post(monkeypatch):
    """Invokes gh api with POST method and correct endpoint."""
    captured = stub_create_issue(monkeypatch, 42)
    classify_file.create_issue(
        _make_args(file="/p/test_foo.cpp"), ["A"],
    )
    assert "-X" in captured[0]["cmd"]


def test_create_issue_returns_number(monkeypatch):
    """Returns the issue number from the API response."""
    stub_create_issue(monkeypatch, 77)
    result = classify_file.create_issue(
        _make_args(file="/p/test_foo.cpp"), ["A"],
    )
    assert result == 77


def test_create_issue_prints_confirmation(monkeypatch, capsys):
    """Prints confirmation with the created issue number."""
    stub_create_issue(monkeypatch, 42)
    classify_file.create_issue(
        _make_args(file="/p/test_foo.cpp"), ["A"],
    )
    assert "Created issue #42" in capsys.readouterr().out


def test_create_issue_exits_on_failure(monkeypatch):
    """Exits when gh api returns non-zero."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        classify_file.create_issue(
            _make_args(file="/p/test_foo.cpp"), ["A"],
        )


# ---- _run ------------------------------------------------------------------


def test_run_file_not_found(tmp_path):
    """Exits when input file does not exist."""
    args = _make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    )
    with pytest.raises(SystemExit):
        _run(args)


def test_run_missing_file_with_issue_closes_issue(
    tmp_path, monkeypatch,
):
    """Missing file + --issue → close_issue called."""
    log = stub_close_issue(monkeypatch)
    _run(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    ))
    assert len(log) == 1


def test_run_missing_file_with_issue_returns(
    tmp_path, monkeypatch,
):
    """Missing file + --issue → returns without SystemExit."""
    stub_close_issue(monkeypatch)
    assert _run(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    )) is None


def test_run_missing_file_without_issue_exits(tmp_path):
    """Missing file + --create-issue → SystemExit."""
    with pytest.raises(SystemExit):
        _run(_make_run_args(
            tmp_path, file=str(tmp_path / "missing.cpp"),
            create_issue=True, issue=None,
        ))


def test_run_no_tests(tmp_path):
    """Exits when file has no TEST blocks."""
    make_test_file(tmp_path, "#include <gtest/gtest.h>\n")
    with pytest.raises(SystemExit):
        _run(_make_run_args(tmp_path))


def test_run_all_succeed(tmp_path, monkeypatch):
    """Does not exit when all tests succeed."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    make_test_file(tmp_path, body)
    stub_ensure_unchecked(monkeypatch)
    captured = stub_subprocess_success(monkeypatch)
    stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path))
    assert len(captured) == 2


def test_run_some_fail_exits(tmp_path, monkeypatch):
    """Exits when any test fails."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    make_test_file(tmp_path, body)
    stub_ensure_unchecked(monkeypatch)
    stub_subprocess_mixed(monkeypatch, {"B"})
    with pytest.raises(SystemExit):
        _run(_make_run_args(tmp_path))


def test_run_stops_after_failure(tmp_path, monkeypatch):
    """Stops immediately when a test fails."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    make_test_file(tmp_path, body)
    stub_ensure_unchecked(monkeypatch)
    captured = stub_subprocess_mixed(monkeypatch, {"A"})
    try:
        _run(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert len(captured) == 1


def test_run_invokes_per_test(tmp_path, monkeypatch):
    """Invokes classify_test once per test name."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    make_test_file(tmp_path, body)
    stub_ensure_unchecked(monkeypatch)
    captured = stub_subprocess_success(monkeypatch)
    stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path))
    assert len(captured) == 3


def test_run_closes_issue_on_success(tmp_path, monkeypatch):
    """Closes issue when all tests succeed."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    stub_ensure_unchecked(monkeypatch)
    stub_subprocess_success(monkeypatch)
    log = stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_skips_close_on_failure(tmp_path, monkeypatch):
    """Does not close issue when tests fail."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    stub_ensure_unchecked(monkeypatch)
    stub_subprocess_failure(monkeypatch)
    log = stub_close_issue(monkeypatch)
    try:
        _run(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert len(log) == 0


def test_run_skips_close_on_dry_run(tmp_path, monkeypatch):
    """Does not close issue in dry-run mode."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    stub_ensure_unchecked(monkeypatch)
    stub_subprocess_success(monkeypatch)
    log = stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path, dry_run=True))
    assert len(log) == 0


def _stub_create_and_run(tmp_path, monkeypatch, **run_overrides):
    """Stub create_issue, subprocess, and close_issue; run pipeline."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    create_log: list[bool] = []
    monkeypatch.setattr(
        classify_file, "create_issue",
        lambda _a, _n: (create_log.append(True), 42)[1],
    )
    stub_ensure_unchecked(monkeypatch)
    captured = stub_subprocess_success(monkeypatch)
    stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path, **run_overrides))
    return create_log, captured


def test_run_creates_issue_when_flag_set(tmp_path, monkeypatch):
    """Calls create_issue when --create-issue is set."""
    create_log, _ = _stub_create_and_run(
        tmp_path, monkeypatch, issue=None, create_issue=True,
    )
    assert len(create_log) == 1


def test_run_sets_issue_from_creation(tmp_path, monkeypatch):
    """Subprocess commands use the issue number from create_issue."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    monkeypatch.setattr(
        classify_file, "create_issue",
        lambda _a, _n: 77,
    )
    captured = stub_subprocess_success(monkeypatch)
    stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path, issue=None, create_issue=True))
    assert captured[0][captured[0].index("--issue") + 1] == "77"


def test_run_skips_create_when_issue_given(tmp_path, monkeypatch):
    """Does not call create_issue when --issue is provided."""
    create_log, _ = _stub_create_and_run(tmp_path, monkeypatch)
    assert len(create_log) == 0


# ---- main ------------------------------------------------------------------


def test_main_calls_run(monkeypatch):
    """Calls _run with parsed args."""
    ran = []
    monkeypatch.setattr(
        classify_file, "_run",
        lambda args: ran.append(True),
    )
    monkeypatch.setattr(
        classify_file, "_parse_args", _make_args,
    )
    classify_file.main()
    assert ran == [True]


def test_main_enables_line_buffering(monkeypatch):
    """Reconfigures stdout to line-buffered mode."""
    configured = []
    original = sys.stdout.reconfigure

    def mock_reconfigure(**kwargs):
        configured.append(kwargs)
        return original(**kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(classify_file, "_run", lambda _: None)
    monkeypatch.setattr(
        classify_file, "_parse_args", _make_args,
    )
    classify_file.main()
    assert any(k.get("line_buffering") for k in configured)


# ---- ensure_unchecked ------------------------------------------------------


ensure_unchecked = classify_file.ensure_unchecked


def _stub_github(monkeypatch, body):
    """Stub fetch_issue_body and capture update_issue_body calls."""
    monkeypatch.setattr(
        classify_file, "fetch_issue_body",
        lambda _o, _r, _i: body,
    )
    updates: list[str] = []
    monkeypatch.setattr(
        classify_file, "update_issue_body",
        lambda _o, _r, _i, b: updates.append(b),
    )
    return updates


def test_ensure_unchecked_all_unchecked_no_update(monkeypatch):
    """Does not call update when all checkboxes are already unchecked."""
    body = "- [ ] Alpha\n- [ ] Beta\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha", "Beta"])
    assert len(updates) == 0


def test_ensure_unchecked_unchecks_checked_box(monkeypatch):
    """Unchecks a checked checkbox."""
    body = "- [x] Alpha\n- [ ] Beta\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha", "Beta"])
    assert "- [ ] Alpha" in updates[0]


def test_ensure_unchecked_adds_missing_box(monkeypatch):
    """Adds an unchecked checkbox for a missing test."""
    body = "- [ ] Alpha\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha", "Beta"])
    assert "- [ ] Beta" in updates[0]


def test_ensure_unchecked_mixed_unchecks(monkeypatch):
    """Mixed: unchecks the checked box."""
    body = "- [x] Alpha\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha", "Beta"])
    assert "- [ ] Alpha" in updates[0]


def test_ensure_unchecked_mixed_adds_missing(monkeypatch):
    """Mixed: adds the missing box."""
    body = "- [x] Alpha\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha", "Beta"])
    assert "- [ ] Beta" in updates[0]


def test_ensure_unchecked_calls_update(monkeypatch):
    """Calls update_issue_body when changes are made."""
    body = "- [x] Alpha\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha"])
    assert len(updates) == 1


def test_ensure_unchecked_preserves_other_checked(monkeypatch):
    """Leaves checked boxes for tests not in test_names."""
    body = "- [x] Other\n- [ ] Alpha\n"
    updates = _stub_github(monkeypatch, body)
    ensure_unchecked(_make_args(), ["Alpha"])
    assert len(updates) == 0


# ---- _run + ensure_unchecked -----------------------------------------------


def test_run_calls_ensure_unchecked_with_issue(
    tmp_path, monkeypatch,
):
    """Calls ensure_unchecked when --issue is provided."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    log = stub_ensure_unchecked(monkeypatch)
    stub_subprocess_success(monkeypatch)
    stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_skips_ensure_unchecked_with_create_issue(
    tmp_path, monkeypatch,
):
    """Does not call ensure_unchecked when --create-issue is used."""
    make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    log = stub_ensure_unchecked(monkeypatch)
    monkeypatch.setattr(
        classify_file, "create_issue",
        lambda _a, _n: 42,
    )
    stub_subprocess_success(monkeypatch)
    stub_close_issue(monkeypatch)
    _run(_make_run_args(tmp_path, issue=None, create_issue=True))
    assert len(log) == 0
