"""Tests for implement_clause core functions."""

import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import pytest


def _patch_main_no_subclauses(monkeypatch, ic):
    """Patch dependencies for the no-subclauses main() path."""
    monkeypatch.setattr(ic, "discover_subclauses", lambda *_a: {})


_ISSUE_COUNTER = iter(range(100, 200))


def _patch_main_with_subclauses(monkeypatch, ic, *, subclauses=None):
    """Patch all dependencies for main() with subclauses."""
    if subclauses is None:
        subclauses = {"4.1": "General", "4.2": "Exec"}

    monkeypatch.setattr(ic, "discover_subclauses", lambda *_a: subclauses)

    mock_create = MagicMock(side_effect=lambda *_a, **_kw: next(_ISSUE_COUNTER))
    monkeypatch.setattr(ic, "create_issue", mock_create)

    mock_update = MagicMock()
    monkeypatch.setattr(ic, "update_issue_body", mock_update)

    mock_inv = MagicMock()
    monkeypatch.setattr(ic, "invoke_implement_subclauses", mock_inv)

    mock_close = MagicMock()
    monkeypatch.setattr(ic, "close_issue", mock_close)

    return {
        "create": mock_create, "update": mock_update,
        "invoke": mock_inv, "close": mock_close,
    }


# --- parse_args ---


def test_parse_args_clause(ic, tmp_path) -> None:
    """--clause flag sets args.clause to the number."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(ic, tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert args.annex == "A"


def test_parse_args_clause_and_annex_exclusive(ic, tmp_path) -> None:
    """--clause and --annex are mutually exclusive."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm), "--clause", "4", "--annex", "A",
            "--issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_missing_lrm(ic) -> None:
    """SystemExit when --lrm points to a nonexistent file."""
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", "/no/such/file", "--clause", "4",
            "--issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_issue_is_int(ic, tmp_path) -> None:
    """--issue is parsed as an integer."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "42",
        "--organization", "o", "--repo", "r",
    ])
    assert args.issue == 42


def test_parse_args_issue_is_optional(ic, tmp_path) -> None:
    """--issue is optional (None when not provided)."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--organization", "o", "--repo", "r",
    ])
    assert args.issue is None


def test_parse_args_no_clause_or_annex(ic, tmp_path) -> None:
    """SystemExit when neither --clause nor --annex is provided."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm),
            "--issue", "1",
            "--organization", "o", "--repo", "r",
        ])


@pytest.mark.parametrize("flag,value", [
    ("--figures", "4_1=fig.gv"),
    ("--tables", "4_1=tbl.md"),
])
def test_parse_args_rejects_removed_flag(ic, tmp_path, flag, value) -> None:
    """Removed flags (--figures, --tables) are no longer accepted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm), "--clause", "4",
            "--issue", "1",
            "--organization", "o", "--repo", "r",
            flag, value,
        ])


# --- main ---


def test_main_no_subclauses_exits(ic, monkeypatch, clause_argv) -> None:
    """Empty discovery causes SystemExit(1)."""
    _patch_main_no_subclauses(monkeypatch, ic)
    with pytest.raises(SystemExit):
        ic.main(clause_argv)


def test_main_no_subclauses_error_message(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Empty discovery prints an error to stderr."""
    _patch_main_no_subclauses(monkeypatch, ic)
    try:
        ic.main(clause_argv)
    except SystemExit:
        pass
    assert "no subclauses" in capsys.readouterr().err.lower()


def test_main_prints_subclauses_found(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Prints how many subclauses were discovered."""
    _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert "Found 2 subclauses" in capsys.readouterr().out


def test_main_creates_subclause_issues(ic, monkeypatch, clause_argv) -> None:
    """main() creates an issue for each discovered subclause."""
    mocks = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mocks["create"].call_count == 2


def test_main_sets_clause_issue_body(ic, monkeypatch, clause_argv) -> None:
    """main() sets the clause issue body to a list of subclause issue refs."""
    mocks = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mocks["update"].called


def test_main_invokes_implement_subclauses(ic, monkeypatch, clause_argv) -> None:
    """main() calls invoke_implement_subclauses."""
    mocks = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mocks["invoke"].call_count == 1


def test_main_closes_clause_issue(ic, monkeypatch, clause_argv) -> None:
    """main() closes the clause issue after all subclauses."""
    mocks = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mocks["close"].called


def test_main_creates_clause_issue_when_absent(
    ic, monkeypatch, tmp_path,
) -> None:
    """main() creates the clause issue when --issue is not provided."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    argv = [
        "--lrm", str(lrm), "--clause", "4",
        "--organization", "o", "--repo", "r",
    ]
    mocks = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(argv)
    assert mocks["create"].call_count >= 3  # 1 clause + 2 subclauses


def test_main_annex(ic, monkeypatch, tmp_path) -> None:
    """Annex flag passes the letter to discover_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    argv = [
        "--lrm", str(lrm), "--annex", "A",
        "--issue", "1",
        "--organization", "o", "--repo", "r",
    ]
    mock_ds = MagicMock(return_value={"A.1": "General"})
    monkeypatch.setattr(ic, "discover_subclauses", mock_ds)
    monkeypatch.setattr(ic, "create_issue", MagicMock(return_value=50))
    monkeypatch.setattr(ic, "update_issue_body", MagicMock())
    monkeypatch.setattr(ic, "invoke_implement_subclauses", MagicMock())
    monkeypatch.setattr(ic, "close_issue", MagicMock())
    ic.main(argv)
    assert mock_ds.call_args[0][1] == "A"


# --- discover_subclauses ---


def test_discover_subclauses_parses_json(ic, monkeypatch) -> None:
    """discover_subclauses parses Claude's JSON response."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General", "4.2": "Exec"}\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.1": "General", "4.2": "Exec"}


def test_discover_subclauses_strips_code_fences(ic, monkeypatch) -> None:
    """discover_subclauses strips markdown code fences from response."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='```json\n{"4.1": "General"}\n```\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.1": "General"}


def test_discover_subclauses_strips_preamble_before_fences(
    ic, monkeypatch,
) -> None:
    """discover_subclauses extracts JSON from fences preceded by prose."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='Here is the JSON:\n\n```json\n{"4.1": "General"}\n```\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.1": "General"}


def _discover_subclauses_cmd(ic, monkeypatch):
    """Helper: run discover_subclauses and return the mock_run object."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General"}\n',
        stderr="",
    )
    mock_run = MagicMock(return_value=cp)
    monkeypatch.setattr(ic, "run_claude_cli", mock_run)
    ic.discover_subclauses(Path("/path/lrm.pdf"), "4")
    return mock_run


def _discover_subclauses_prompt(ic, monkeypatch):
    """Helper: run discover_subclauses and return the prompt string."""
    mock_run = _discover_subclauses_cmd(ic, monkeypatch)
    return mock_run.call_args[0][1]


def test_discover_subclauses_prompt_contains_clause(
    ic, monkeypatch,
) -> None:
    """discover_subclauses prompt references the clause number."""
    prompt = _discover_subclauses_prompt(ic, monkeypatch)
    assert "clause 4" in prompt.lower() or "§4" in prompt


def test_discover_subclauses_prompt_contains_lrm_path(
    ic, monkeypatch,
) -> None:
    """discover_subclauses prompt references the LRM PDF path."""
    prompt = _discover_subclauses_prompt(ic, monkeypatch)
    assert "/path/lrm.pdf" in prompt


def test_discover_subclauses_exits_on_claude_failure(
    ic, monkeypatch,
) -> None:
    """discover_subclauses exits when Claude CLI fails."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="error",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    with pytest.raises(SystemExit):
        ic.discover_subclauses(Path("/lrm.pdf"), "4")


def test_discover_subclauses_empty_result(ic, monkeypatch) -> None:
    """discover_subclauses returns empty dict when response is empty."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{}\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {}


def test_discover_subclauses_default_model_is_opus(ic, monkeypatch) -> None:
    """discover_subclauses uses --model opus by default."""
    mock_run = _discover_subclauses_cmd(ic, monkeypatch)
    cmd = mock_run.call_args[0][0]
    idx = cmd.index("--model")
    assert cmd[idx + 1] == "opus"


def test_discover_subclauses_passes_effort_high(ic, monkeypatch) -> None:
    """discover_subclauses passes --effort high to Claude CLI."""
    mock_run = _discover_subclauses_cmd(ic, monkeypatch)
    cmd = mock_run.call_args[0][0]
    idx = cmd.index("--effort")
    assert cmd[idx + 1] == "high"


def test_discover_subclauses_uses_dangerously_skip_permissions(
    ic, monkeypatch,
) -> None:
    """discover_subclauses passes --dangerously-skip-permissions."""
    mock_run = _discover_subclauses_cmd(ic, monkeypatch)
    assert "--dangerously-skip-permissions" in mock_run.call_args[0][0]


def test_discover_subclauses_excludes_parent_clause(
    ic, monkeypatch,
) -> None:
    """discover_subclauses filters out the parent clause itself."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"15": "Processes", "15.1": "General"}\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "15")
    assert result == {"15.1": "General"}


def test_discover_subclauses_uses_run_with_dots(ic, monkeypatch):
    """discover_subclauses calls run_with_dots for progress feedback."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General"}\n',
        stderr="",
    )
    mock_rwd = MagicMock(return_value=cp)
    monkeypatch.setattr(ic, "run_with_dots", mock_rwd)
    ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert mock_rwd.called
