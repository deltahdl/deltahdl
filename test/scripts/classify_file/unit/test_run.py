"""Unit tests for run-flow functions in classify_file."""

import sys
from pathlib import Path

import pytest

from lib.python.test_fixtures import (
    CLASSIFY_BASE_ARGV,
    argv_without_flag,
    main_enables_line_buffering,
    capture_help_output,
    make_classify_args,
)
from lib.python.test_fixtures.subprocess_stubs import spy_subprocess_run


# ---- Shared helpers --------------------------------------------------------


_BASE_ARGV = [
    "prog", "--file", "f.cpp",
    "--issue", "99",
    *CLASSIFY_BASE_ARGV,
]


def _make_args(**overrides):
    """Build args with classify_file-specific defaults."""
    defaults = {"issue": 99, "create_issue": False}
    defaults.update(overrides)
    return make_classify_args(**defaults)


def _make_run_args(tmp_path, **overrides):
    """Build args for _run with a real test file."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "lrm": str(tmp_path / "lrm.txt"),
        "issue": 99,
        "create_issue": False,
    }
    defaults.update(overrides)
    return make_classify_args(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_file(monkeypatch, cf):
    """Parses --file flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().file == "f.cpp"


def test_parse_args_output_dir(monkeypatch, cf):
    """Parses --output-dir flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().output_dir == "/out"


def test_parse_args_lrm(monkeypatch, cf):
    """Parses --lrm flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().lrm == "/lrm.txt"


def test_parse_args_prog_name(monkeypatch, cf, capsys):
    """Usage line shows 'classify_file' as program name."""
    assert "classify_file" in capture_help_output(
        getattr(cf, "_parse_args"), monkeypatch, capsys,
    )


def test_parse_args_issue(monkeypatch, cf):
    """Parses --issue as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--issue", "42"],
    )
    assert getattr(cf, "_parse_args")().issue == 42


def test_parse_args_create_issue(monkeypatch, cf):
    """Parses --create-issue flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue" and v != "--issue"]
    monkeypatch.setattr(
        sys, "argv", [*argv, "--create-issue"],
    )
    assert getattr(cf, "_parse_args")().create_issue is True


def test_parse_args_create_issue_default_false(monkeypatch, cf):
    """Defaults --create-issue to False when --issue is given."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().create_issue is False


def test_parse_args_neither_issue_flag_rejects(monkeypatch, cf):
    """Rejects when neither --issue nor --create-issue is given."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue" and v != "--issue"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_both_issue_flags_reject(monkeypatch, cf):
    """Rejects when both --issue and --create-issue are given."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--create-issue"],
    )
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_organization(monkeypatch, cf):
    """Parses --organization flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--organization", "myorg"],
    )
    assert getattr(cf, "_parse_args")().organization == "myorg"


def test_parse_args_organization_required(monkeypatch, cf):
    """Rejects missing --organization flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--organization"
            and v != "--organization"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_repo(monkeypatch, cf):
    """Parses --repo flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--repo", "myrepo"],
    )
    assert getattr(cf, "_parse_args")().repo == "myrepo"


def test_parse_args_repo_required(monkeypatch, cf):
    """Rejects missing --repo flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--repo"
            and v != "--repo"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_dry_run(monkeypatch, cf):
    """Parses --dry-run flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--dry-run"],
    )
    assert getattr(cf, "_parse_args")().dry_run is True


def test_parse_args_dry_run_default(monkeypatch, cf):
    """Defaults --dry-run to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().dry_run is False



def test_parse_args_max_lines(monkeypatch, cf):
    """Parses --max-lines as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert getattr(cf, "_parse_args")().max_lines == 500


def test_parse_args_max_lines_required(monkeypatch, cf):
    """Rejects missing --max-lines flag."""
    monkeypatch.setattr(
        sys, "argv", argv_without_flag(_BASE_ARGV, "--max-lines"),
    )
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_no_test_flag(monkeypatch, cf):
    """Rejects the --test flag since classify_file does not accept it."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--test", "T"],
    )
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


# ---- _build_command --------------------------------------------------------


def test_build_command_basic(cf):
    """Command starts with python -m classify_tests."""
    cmd = getattr(cf, "_build_command")(_make_args(), [("S", "T")])
    assert cmd[:3] == [sys.executable, "-m", "classify_tests"]


def test_build_command_file_flag(cf):
    """Command includes --file with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(file="/a/b.cpp"), [("S", "T")])
    assert cmd[cmd.index("--file") + 1] == "/a/b.cpp"


def test_build_command_output_dir_flag(cf):
    """Command includes --output-dir with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(output_dir="/out"), [("S", "T")])
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag(cf):
    """Command includes --lrm with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(lrm="/lrm.txt"), [("S", "T")])
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_tests_flag(cf):
    """Command includes --tests with Suite.Test pairs."""
    cmd = getattr(cf, "_build_command")(
        _make_args(), [("S", "A"), ("S", "B"), ("X", "C")],
    )
    assert cmd[cmd.index("--tests") + 1] == "S.A,S.B,X.C"


def test_build_command_issue_included(cf):
    """Command includes --issue with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(issue=42), [("S", "T")])
    assert cmd[cmd.index("--issue") + 1] == "42"


def test_build_command_organization_included(cf):
    """Command includes --organization."""
    cmd = getattr(cf, "_build_command")(_make_args(), [("S", "T")])
    assert cmd[cmd.index("--organization") + 1] == "testorg"


def test_build_command_repo_included(cf):
    """Command includes --repo."""
    cmd = getattr(cf, "_build_command")(_make_args(), [("S", "T")])
    assert cmd[cmd.index("--repo") + 1] == "testrepo"


def test_build_command_dry_run_included(cf):
    """Command includes --dry-run when set."""
    cmd = getattr(cf, "_build_command")(_make_args(dry_run=True), [("S", "T")])
    assert "--dry-run" in cmd


def test_build_command_dry_run_omitted(cf):
    """Command omits --dry-run when not set."""
    cmd = getattr(cf, "_build_command")(_make_args(), [("S", "T")])
    assert "--dry-run" not in cmd


def test_build_command_no_commit_included(cf):
    """Command includes --no-commit when set."""
    cmd = getattr(cf, "_build_command")(_make_args(no_commit=True), [("S", "T")])
    assert "--no-commit" in cmd


def test_build_command_no_commit_omitted(cf):
    """Command omits --no-commit when not set."""
    cmd = getattr(cf, "_build_command")(_make_args(), [("S", "T")])
    assert "--no-commit" not in cmd


def test_build_command_max_lines_included(cf):
    """Command includes --max-lines."""
    cmd = getattr(cf, "_build_command")(_make_args(), [("S", "T")])
    assert cmd[cmd.index("--max-lines") + 1] == "1000"


def test_build_command_max_lines_value(cf):
    """Command passes --max-lines with correct string value."""
    cmd = getattr(cf, "_build_command")(_make_args(max_lines=500), [("S", "T")])
    assert cmd[cmd.index("--max-lines") + 1] == "500"


# ---- run_classify_tests ----------------------------------------------------


def test_run_classify_tests_returns_true_on_success(monkeypatch, cf, cf_helpers):
    """Returns True when subprocess exits with 0."""
    cf_helpers.stub_subprocess_success(monkeypatch)
    assert cf.run_classify_tests(_make_args(), [("S", "T")]) is True


def test_run_classify_tests_returns_false_on_failure(monkeypatch, cf, cf_helpers):
    """Returns False when subprocess exits with non-zero."""
    cf_helpers.stub_subprocess_failure(monkeypatch)
    assert cf.run_classify_tests(_make_args(), [("S", "T")]) is False


def test_run_classify_tests_does_not_capture_output(monkeypatch, cf):
    """Subprocess inherits stdout/stderr (no capture_output)."""
    kwargs_log = spy_subprocess_run(monkeypatch)
    cf.run_classify_tests(_make_args(), [("S", "T")])
    assert "capture_output" not in kwargs_log[0]


# ---- build_issue_body ------------------------------------------------------


def test_build_issue_body_table_header(cf):
    """Body contains the table header row."""
    assert "| Suite | Test | Status | Action |" in cf.build_issue_body(
        [("S", "A"), ("S", "B"), ("S", "C")],
    )


def test_build_issue_body_rows(cf):
    """Body contains table rows for each test pair."""
    body = cf.build_issue_body([("X", "Alpha"), ("Y", "Beta")])
    assert "| X | Alpha | Unreviewed | |" in body


def test_build_issue_body_single_test(cf):
    """Body works correctly with a single test."""
    assert "| S | Only | Unreviewed | |" in cf.build_issue_body(
        [("S", "Only")],
    )


def test_build_issue_body_no_summary_heading(cf):
    """Body does not contain Summary heading."""
    assert "## Summary" not in cf.build_issue_body([("S", "A")])


def test_build_issue_body_no_tests_heading(cf):
    """Body does not contain Tests heading."""
    assert "## Tests" not in cf.build_issue_body([("S", "A")])


# ---- create_issue ----------------------------------------------------------


def test_create_issue_calls_gh_api_post(monkeypatch, cf, cf_helpers):
    """Invokes gh api with POST method and correct endpoint."""
    captured = cf_helpers.stub_create_issue(monkeypatch, 42)
    cf.create_issue(
        _make_args(file="/p/test_foo.cpp"), [("S", "A")],
    )
    assert "-X" in captured[0]["cmd"]


def test_create_issue_returns_number(monkeypatch, cf, cf_helpers):
    """Returns the issue number from the API response."""
    cf_helpers.stub_create_issue(monkeypatch, 77)
    result = cf.create_issue(
        _make_args(file="/p/test_foo.cpp"), [("S", "A")],
    )
    assert result == 77


def test_create_issue_prints_confirmation(monkeypatch, cf, cf_helpers, capsys):
    """Prints confirmation with the created issue number."""
    cf_helpers.stub_create_issue(monkeypatch, 42)
    cf.create_issue(
        _make_args(file="/p/test_foo.cpp"), [("S", "A")],
    )
    assert "Created issue #42" in capsys.readouterr().out


def test_create_issue_exits_on_failure(monkeypatch, cf, cf_helpers):
    """Exits when gh api returns non-zero."""
    cf_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        cf.create_issue(
            _make_args(file="/p/test_foo.cpp"), [("S", "A")],
        )


# ---- _run ------------------------------------------------------------------


def test_run_file_not_found(tmp_path, cf):
    """Returns cleanly when input file does not exist."""
    args = _make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    )
    assert getattr(cf, "_run")(args) is None


def test_run_missing_file_prints_not_found(tmp_path, cf, capsys):
    """Missing file prints 'not found' message to stdout."""
    getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    ))
    assert "not found" in capsys.readouterr().out


def test_run_missing_file_with_issue_closes_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Missing file + --issue → close_issue called."""
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    ))
    assert len(log) == 1


def test_run_missing_file_with_issue_returns(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Missing file + --issue → returns without SystemExit."""
    cf_helpers.stub_close_issue(monkeypatch)
    assert getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    )) is None


def test_run_missing_file_with_create_issue_returns(tmp_path, cf):
    """Missing file + --create-issue → returns without SystemExit."""
    assert getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    )) is None


def test_run_no_tests_with_issue_deletes_file(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → file is deleted."""
    f = cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert not f.exists()


def test_run_no_tests_with_issue_closes_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → close_issue called."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_no_tests_with_issue_returns(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → returns without SystemExit."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    assert getattr(cf, "_run")(_make_run_args(tmp_path)) is None


def test_run_no_tests_with_create_issue_deletes_file(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --create-issue → file is deleted."""
    f = cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, create_issue=True, issue=None,
    ))
    assert not f.exists()


def test_run_no_tests_with_create_issue_returns(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --create-issue → returns without SystemExit."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    assert getattr(cf, "_run")(_make_run_args(
        tmp_path, create_issue=True, issue=None,
    )) is None


def test_run_no_tests_prints_deleting(
    tmp_path, capsys, monkeypatch, cf, cf_helpers,
):
    """Empty file → stdout explains why file is being deleted."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "because it contains no tests" in capsys.readouterr().out


def test_run_no_tests_prints_deleted(
    tmp_path, capsys, monkeypatch, cf, cf_helpers,
):
    """Empty file → stdout contains 'Deleted'."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "Deleted" in capsys.readouterr().out


def test_run_no_tests_with_issue_commits_deletion(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → commit_and_push called with deleted filepath."""
    cf_helpers.make_test_file(tmp_path, "")
    log = []
    monkeypatch.setattr(
        cf, "commit_and_push",
        lambda changed, deleted, msg: log.append((changed, deleted, msg)),
    )
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def _run_empty_file_skip_commit(tmp_path, monkeypatch, cf, cf_helpers, **kw):
    """Shared setup: empty file with commit_and_push stubbed out."""
    cf_helpers.make_test_file(tmp_path, "")
    log = []
    monkeypatch.setattr(
        cf, "commit_and_push",
        lambda changed, deleted, msg: log.append(1),
    )
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, **kw))
    return log


def test_run_no_tests_with_issue_dry_run_skips_commit(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue + --dry-run → commit_and_push not called."""
    log = _run_empty_file_skip_commit(
        tmp_path, monkeypatch, cf, cf_helpers, dry_run=True,
    )
    assert len(log) == 0


def test_run_no_tests_with_issue_no_commit_skips_commit(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue + --no-commit → commit_and_push not called."""
    log = _run_empty_file_skip_commit(
        tmp_path, monkeypatch, cf, cf_helpers, no_commit=True,
    )
    assert len(log) == 0


def test_run_all_succeed(tmp_path, monkeypatch, cf, cf_helpers):
    """Does not exit when all tests succeed."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(captured) == 1


def test_run_fail_exits(tmp_path, monkeypatch, cf, cf_helpers):
    """Exits when classify_tests fails."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        getattr(cf, "_run")(_make_run_args(tmp_path))


def test_run_invokes_classify_tests_once(tmp_path, monkeypatch, cf, cf_helpers):
    """Invokes classify_tests once with all test names."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(captured) == 1


def test_run_passes_tests_flag(tmp_path, monkeypatch, cf, cf_helpers):
    """Passes --tests with comma-joined names."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    cmd = captured[0]
    assert cmd[cmd.index("--tests") + 1] == "S.A,S.B"


def test_run_closes_issue_on_success(tmp_path, monkeypatch, cf, cf_helpers):
    """Closes issue when all tests succeed."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_skips_close_on_failure(tmp_path, monkeypatch, cf, cf_helpers):
    """Does not close issue when tests fail."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_failure(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    try:
        getattr(cf, "_run")(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert len(log) == 0


def test_run_skips_close_on_dry_run(tmp_path, monkeypatch, cf, cf_helpers):
    """Does not close issue in dry-run mode."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, dry_run=True))
    assert len(log) == 0


def test_run_close_reason_all_classified(
    tmp_path, monkeypatch, cf, cf_helpers, capsys,
):
    """Closes with 'all tests have been classified' on success."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "because all tests have been classified" \
           in capsys.readouterr().out


def test_run_close_reason_no_tests(
    tmp_path, monkeypatch, cf, cf_helpers, capsys,
):
    """Closes with 'the file has no tests' when file is empty."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "because the file has no tests" in capsys.readouterr().out


def test_run_close_reason_file_missing(
    tmp_path, monkeypatch, cf, cf_helpers, capsys,
):
    """Closes with 'the source file no longer exists' when missing."""
    cf_helpers.stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    ))
    assert "because the source file no longer exists" \
           in capsys.readouterr().out


def _stub_create_and_run(
    cf, cf_helpers, tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch, **run_overrides: object,
) -> tuple[list[bool], list[list[str]]]:
    """Stub create_issue, subprocess, and close_issue; run pipeline."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    create_log: list[bool] = []
    def fake_create(_a: object, _n: object) -> int:
        create_log.append(True)
        return 42

    monkeypatch.setattr(cf, "create_issue", fake_create)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, **run_overrides))
    return create_log, captured


def test_run_creates_issue_when_flag_set(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Calls create_issue when --create-issue is set."""
    create_log, _ = _stub_create_and_run(
        cf, cf_helpers, tmp_path, monkeypatch,
        issue=None, create_issue=True,
    )
    assert len(create_log) == 1


def test_run_sets_issue_from_creation(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Subprocess commands use the issue number from create_issue."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    monkeypatch.setattr(cf, "create_issue", lambda _a, _n: 77)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, issue=None, create_issue=True,
    ))
    assert captured[0][captured[0].index("--issue") + 1] == "77"


def test_run_skips_create_when_issue_given(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not call create_issue when --issue is provided."""
    create_log, _ = _stub_create_and_run(
        cf, cf_helpers, tmp_path, monkeypatch,
    )
    assert len(create_log) == 0


# ---- main ------------------------------------------------------------------


def test_main_calls_run(monkeypatch, cf):
    """Calls _run with parsed args."""
    ran = []
    monkeypatch.setattr(cf, "_run", lambda args: ran.append(True))
    monkeypatch.setattr(cf, "_parse_args", _make_args)
    cf.main()
    assert ran == [True]


def test_main_enables_line_buffering(monkeypatch, cf):
    """Reconfigures stdout to line-buffered mode."""
    assert main_enables_line_buffering(monkeypatch, cf, _make_args)


# ---- sync_issue_rows -------------------------------------------------------


def _stub_github(monkeypatch, cf, body):
    """Stub fetch_issue_body and capture update_issue_body calls."""
    monkeypatch.setattr(
        cf, "fetch_issue_body",
        lambda _o, _r, _i: body,
    )
    updates: list[str] = []
    monkeypatch.setattr(
        cf, "update_issue_body",
        lambda _o, _r, _i, b: updates.append(b),
    )
    return updates


def _table(*rows):
    """Build a full issue table body with header and data rows."""
    header = (
        "| Suite | Test | Status | Action |\n"
        "|-------|------|--------|--------|\n"
    )
    return header + "\n".join(rows) + "\n"


def test_sync_issue_rows_all_unreviewed_no_update(monkeypatch, cf):
    """Does not call update when all rows already match."""
    body = _table(
        "| S | Alpha | Unreviewed | |",
        "| S | Beta | Unreviewed | |",
    )
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), [("S", "Alpha"), ("S", "Beta")])
    assert len(updates) == 0


def test_sync_issue_rows_all_unreviewed_returns_empty(monkeypatch, cf):
    """Returns empty set when all rows are Unreviewed."""
    body = _table(
        "| S | Alpha | Unreviewed | |",
        "| S | Beta | Unreviewed | |",
    )
    _stub_github(monkeypatch, cf, body)
    assert cf.sync_issue_rows(
        _make_args(), [("S", "Alpha"), ("S", "Beta")],
    ) == set()


def test_sync_issue_rows_adds_missing_row(monkeypatch, cf):
    """Rebuilds table with all tests when one is missing."""
    body = _table("| S | Alpha | Unreviewed | |")
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), [("S", "Alpha"), ("S", "Beta")])
    assert "| S | Beta | Unreviewed | |" in updates[0]


def test_sync_issue_rows_missing_returns_empty(monkeypatch, cf):
    """Returns empty set when only missing tests are added."""
    body = _table("| S | Alpha | Unreviewed | |")
    _stub_github(monkeypatch, cf, body)
    assert cf.sync_issue_rows(
        _make_args(), [("S", "Alpha"), ("S", "Beta")],
    ) == set()


def test_sync_issue_rows_removes_stale_rows(monkeypatch, cf):
    """Removes rows for tests not in test_pairs."""
    body = _table(
        "| S | Other | Reviewed | Kept |",
        "| S | Alpha | Unreviewed | |",
    )
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), [("S", "Alpha")])
    assert len(updates) == 1
    assert "Other" not in updates[0]


def test_sync_issue_rows_returns_reviewed(monkeypatch, cf):
    """Returns reviewed test names."""
    body = _table(
        "| S | Alpha | Reviewed | Kept |",
        "| S | Beta | Unreviewed | |",
    )
    _stub_github(monkeypatch, cf, body)
    result = cf.sync_issue_rows(
        _make_args(), [("S", "Alpha"), ("S", "Beta")],
    )
    assert result == {"Alpha"}


def test_sync_issue_rows_preserves_reviewed_status(monkeypatch, cf):
    """Carries over Reviewed status and action into the rebuilt table."""
    body = _table(
        "| S | Alpha | Reviewed | Kept |",
        "| S | Beta | Unreviewed | |",
    )
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(
        _make_args(), [("S", "Alpha"), ("S", "Beta")],
    )
    assert len(updates) == 0


def test_sync_issue_rows_returns_moved(monkeypatch, cf):
    """Returns moved test names."""
    body = _table(
        "| S | Alpha | Reviewed | Moved to target.cpp |",
        "| S | Beta | Unreviewed | |",
    )
    _stub_github(monkeypatch, cf, body)
    result = cf.sync_issue_rows(
        _make_args(), [("S", "Alpha"), ("S", "Beta")],
    )
    assert result == {"Alpha"}


def test_sync_issue_rows_mixed_returns_reviewed(monkeypatch, cf):
    """Returns reviewed names when mixed with missing tests."""
    body = _table("| S | Alpha | Reviewed | Kept |")
    _stub_github(monkeypatch, cf, body)
    result = cf.sync_issue_rows(
        _make_args(), [("S", "Alpha"), ("S", "Beta")],
    )
    assert result == {"Alpha"}


def test_sync_issue_rows_mixed_adds_missing(monkeypatch, cf):
    """Adds missing test row when mixed with reviewed tests."""
    body = _table("| S | Alpha | Reviewed | Kept |")
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), [("S", "Alpha"), ("S", "Beta")])
    assert "| S | Beta | Unreviewed | |" in updates[0]


# ---- _run + sync_issue_rows ------------------------------------------------


def test_run_calls_sync_issue_rows_with_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Calls sync_issue_rows when --issue is provided."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    log = cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_skips_sync_issue_rows_with_create_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not call sync_issue_rows when --create-issue is used."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    log = cf_helpers.stub_sync_issue_rows(monkeypatch)
    monkeypatch.setattr(cf, "create_issue", lambda _a, _n: 42)
    cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, issue=None, create_issue=True,
    ))
    assert len(log) == 0


def _run_with_all_reviewed(tmp_path, monkeypatch, cf, cf_helpers):
    """Run _run() with sync_issue_rows marking all tests as reviewed."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    monkeypatch.setattr(cf, "sync_issue_rows", lambda _a, _n: {"A"})
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    close_log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    return captured, close_log


def _run_with_one_reviewed(tmp_path, monkeypatch, cf, cf_helpers):
    """Run _run() with A reviewed and B unreviewed; return captured cmds."""
    cf_helpers.make_test_file(
        tmp_path, "TEST(S, A) {\n}\nTEST(S, B) {\n}\n",
    )
    monkeypatch.setattr(cf, "sync_issue_rows", lambda _a, _n: {"A"})
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    return captured


def test_run_skips_reviewed_tests_count(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Only invokes classify_tests for unreviewed tests."""
    captured = _run_with_one_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
    )
    assert len(captured) == 1


def test_run_skips_reviewed_tests_name(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Invokes classify_tests for the unreviewed test only."""
    captured = _run_with_one_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
    )
    assert "B" in " ".join(captured[0])


def test_run_all_reviewed_skips_classify(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not invoke classify_tests when all tests are reviewed."""
    captured, _ = _run_with_all_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
    )
    assert len(captured) == 0


def test_run_all_reviewed_closes_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Closes issue when all tests are already reviewed."""
    _, close_log = _run_with_all_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
    )
    assert len(close_log) == 1


def test_run_all_reviewed_dry_run_skips_close(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not close issue when all reviewed and dry_run is set."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    monkeypatch.setattr(cf, "sync_issue_rows", lambda _a, _n: {"A"})
    cf_helpers.stub_subprocess_success(monkeypatch)
    close_log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, dry_run=True))
    assert len(close_log) == 0
