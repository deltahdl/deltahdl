"""Unit tests for implement_clauses (arg parsing and dispatch)."""

import runpy
from unittest.mock import MagicMock

import pytest


# ---- parse_args --------------------------------------------------------------


def test_parse_args_clauses_parsed(icls, base_argv):
    """--clauses is parsed into a dict."""
    assert icls.parse_args(base_argv).clauses == {"15": 17, "16": 18}


def test_parse_args_master_issue_is_int(icls, base_argv):
    """--master-issue is parsed as an integer."""
    assert icls.parse_args(base_argv).master_issue == 1


def test_parse_args_organization(icls, base_argv):
    """--organization is parsed correctly."""
    assert icls.parse_args(base_argv).organization == "o"


def test_parse_args_repo(icls, base_argv):
    """--repo is parsed correctly."""
    assert icls.parse_args(base_argv).repo == "r"


def test_parse_args_rejects_missing_lrm(icls, tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        icls.parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--clauses", "15=17",
            "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_rejects_bad_clauses(icls, tmp_path):
    """Invalid clause format exits."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    with pytest.raises(SystemExit):
        icls.parse_args([
            "--lrm", str(lrm), "--clauses", "bad=17",
            "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_requires_clauses(icls, tmp_path):
    """--clauses is required."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    with pytest.raises(SystemExit):
        icls.parse_args([
            "--lrm", str(lrm),
            "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_requires_master_issue(icls, tmp_path):
    """--master-issue is required."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    with pytest.raises(SystemExit):
        icls.parse_args([
            "--lrm", str(lrm), "--clauses", "15=17",
            "--organization", "o", "--repo", "r",
        ])


# ---- main -------------------------------------------------------------------


def _patch_main(monkeypatch, icls):
    """Patch invoke_implement_clause and return the mock."""
    mock_invoke = MagicMock()
    monkeypatch.setattr(icls, "invoke_implement_clause", mock_invoke)
    return mock_invoke


def test_main_invokes_each_clause(icls, monkeypatch, base_argv):
    """main() invokes implement_clause for each clause."""
    mock_invoke = _patch_main(monkeypatch, icls)
    icls.main(base_argv)
    assert mock_invoke.call_count == 2


def test_main_passes_correct_clause(icls, monkeypatch, base_argv):
    """main() passes clause strings to invoke_implement_clause."""
    mock_invoke = _patch_main(monkeypatch, icls)
    icls.main(base_argv)
    clauses = [call[0][1] for call in mock_invoke.call_args_list]
    assert set(clauses) == {"15", "16"}


def test_main_passes_correct_sub_issues(icls, monkeypatch, base_argv):
    """main() passes sub_issue ints to invoke_implement_clause."""
    mock_invoke = _patch_main(monkeypatch, icls)
    icls.main(base_argv)
    pairs = {call[0][1]: call[0][2] for call in mock_invoke.call_args_list}
    assert pairs == {"15": 17, "16": 18}


def test_main_passes_master_issue(icls, monkeypatch, base_argv):
    """main() passes master_issue to invoke_implement_clause."""
    mock_invoke = _patch_main(monkeypatch, icls)
    icls.main(base_argv)
    assert mock_invoke.call_args_list[0][0][0].master_issue == 1


def test_main_passes_organization(icls, monkeypatch, base_argv):
    """main() passes organization to invoke_implement_clause."""
    mock_invoke = _patch_main(monkeypatch, icls)
    icls.main(base_argv)
    assert mock_invoke.call_args_list[0][0][0].organization == "o"


def test_main_passes_repo(icls, monkeypatch, base_argv):
    """main() passes repo to invoke_implement_clause."""
    mock_invoke = _patch_main(monkeypatch, icls)
    icls.main(base_argv)
    assert mock_invoke.call_args_list[0][0][0].repo == "r"


# ---- __main__ guard ---------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_clauses", run_name="__main__")
