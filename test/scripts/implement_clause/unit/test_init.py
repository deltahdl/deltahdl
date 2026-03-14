"""Tests for implement_clause core functions."""

import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import pytest


def _patch_main_no_subclauses(monkeypatch, ic):
    """Patch dependencies for the no-subclauses main() path."""
    monkeypatch.setattr(ic, "discover_subclauses", lambda *_a: {})
    monkeypatch.setattr(ic, "invoke_implement_subclauses", MagicMock())


def _patch_main_with_subclauses(
    monkeypatch, ic, *, subclauses=None,
    synced_body="body",
):
    """Patch all dependencies for main() with subclauses."""
    if subclauses is None:
        subclauses = {"4.1": "General", "4.2": "Exec"}

    monkeypatch.setattr(ic, "discover_subclauses", lambda *_a: subclauses)
    monkeypatch.setattr(ic, "fetch_issue_body", lambda *_a: "")
    monkeypatch.setattr(ic, "build_synced_body", lambda *_a: synced_body)

    mock_update = MagicMock()
    monkeypatch.setattr(ic, "update_issue_body", mock_update)

    mock_inv = MagicMock()
    monkeypatch.setattr(ic, "invoke_implement_subclauses", mock_inv)

    return mock_inv, mock_update


# --- parse_args ---


def test_parse_args_clause(ic, tmp_path) -> None:
    """--clause flag sets args.clause to the number."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(ic, tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--sub-issue", "1", "--master-issue", "99",
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
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_missing_lrm(ic) -> None:
    """SystemExit when --lrm points to a nonexistent file."""
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", "/no/such/file", "--clause", "4",
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
        ])


def _parse_issue_args(ic, tmp_path):
    """Parse args with --sub-issue 42 --master-issue 1."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "42", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])


def test_parse_args_sub_issue_is_int(ic, tmp_path) -> None:
    """--sub-issue is parsed as an integer."""
    assert _parse_issue_args(ic, tmp_path).sub_issue == 42


def test_parse_args_master_issue_is_int(ic, tmp_path) -> None:
    """--master-issue is parsed as an integer."""
    assert _parse_issue_args(ic, tmp_path).master_issue == 1


def test_parse_args_no_clause_or_annex(ic, tmp_path) -> None:
    """SystemExit when neither --clause nor --annex is provided."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm),
            "--sub-issue", "1", "--master-issue", "99",
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
            "--sub-issue", "1", "--master-issue", "99",
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
    assert "no implementable subclauses" in capsys.readouterr().err.lower()


def test_main_prints_subclauses_found(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Prints how many subclauses were discovered."""
    _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert "Found 2 subclauses" in capsys.readouterr().out


def test_main_prints_synced_body(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Prints the synced issue body."""
    _patch_main_with_subclauses(
        monkeypatch, ic,
        synced_body="## Subclauses\n\n- [ ] 4.1 General\n",
    )
    ic.main(clause_argv)
    assert "## Subclauses" in capsys.readouterr().out


def test_main_syncs_issue_body(ic, monkeypatch, clause_argv) -> None:
    """main() updates the issue body with synced checklist."""
    _, mock_update = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mock_update.call_count == 1


def test_main_passes_all_subclauses(ic, monkeypatch, clause_argv) -> None:
    """main() passes all discovered subclauses to invoke_implement_subclauses."""
    mock_inv, _ = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert set(mock_inv.call_args[0][1]) == {"4.1", "4.2"}


def test_main_passes_clause_issue(ic, monkeypatch, clause_argv) -> None:
    """main() passes sub_issue as clause_issue."""
    mock_inv, _ = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mock_inv.call_args[0][2] == 1


def test_main_with_subclauses(ic, monkeypatch, clause_argv) -> None:
    """invoke_implement_subclauses is called once."""
    mock_inv, _ = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mock_inv.call_count == 1


def test_main_annex(ic, monkeypatch, tmp_path) -> None:
    """Annex flag passes the letter to discover_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    argv = [
        "--lrm", str(lrm), "--annex", "A",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ]
    mock_ds = MagicMock(return_value={"A.1": "General"})
    monkeypatch.setattr(ic, "discover_subclauses", mock_ds)
    monkeypatch.setattr(ic, "fetch_issue_body", lambda *_a: "")
    monkeypatch.setattr(ic, "build_synced_body", lambda *_a: "body")
    monkeypatch.setattr(ic, "update_issue_body", lambda *_a, **_kw: None)
    monkeypatch.setattr(ic, "invoke_implement_subclauses", MagicMock())
    ic.main(argv)
    assert mock_ds.call_args[0][1] == "A"


# --- discover_subclauses ---


def test_discover_subclauses_parses_json(ic, monkeypatch) -> None:
    """discover_subclauses parses Claude's JSON response."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General", "4.2": "Exec", "4.3": false}\n',
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
    """discover_subclauses returns empty dict when all false."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": false}\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {}


def test_discover_subclauses_rationale_is_implementable(
    ic, monkeypatch,
) -> None:
    """Subclauses with string rationale are treated as implementable."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "Defines syntax rules that must be parsed"}\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert "4.1" in result


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


def test_discover_subclauses_bool_true_is_implementable(
    ic, monkeypatch,
) -> None:
    """Subclauses with value true are treated as implementable."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.2": true}\n',
        stderr="",
    )
    monkeypatch.setattr(ic, "run_claude_cli", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.2": "4.2"}


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
