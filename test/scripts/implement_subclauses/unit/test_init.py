"""Unit tests for implement_subclauses (arg parsing and dispatch)."""

import runpy
from unittest.mock import MagicMock

import pytest


# ---- _extract_subclause_from_title ------------------------------------------


def test_extract_subclause_numeric(iscs):
    """Extracts numeric subclause from title."""
    extract = getattr(iscs, "_extract_subclause_from_title")
    title = (
        "Ensure IEEE 1800-2023 §3.1"
        " functionalities and tests are implemented"
    )
    assert extract(title) == "3.1"


def test_extract_subclause_annex(iscs):
    """Extracts annex subclause from title."""
    extract = getattr(iscs, "_extract_subclause_from_title")
    title = (
        "Ensure IEEE 1800-2023 A.1.1"
        " functionalities and tests are implemented"
    )
    assert extract(title) == "A.1.1"


def test_extract_subclause_not_found(iscs):
    """Returns empty string when no subclause found."""
    extract = getattr(iscs, "_extract_subclause_from_title")
    assert extract("Some other title") == ""


# ---- parse_args -------------------------------------------------------------


def test_parse_args_issues_parsed(iscs, base_argv):
    """--issues is parsed into a list of ints."""
    assert iscs.parse_args(base_argv).issues == [100, 101]


def test_parse_args_organization(iscs, base_argv):
    """--organization is parsed correctly."""
    assert iscs.parse_args(base_argv).organization == "o"


def test_parse_args_repo(iscs, base_argv):
    """--repo is parsed correctly."""
    assert iscs.parse_args(base_argv).repo == "r"


def test_parse_args_model_default(iscs, base_argv):
    """--model defaults to opus."""
    assert iscs.parse_args(base_argv).model == "opus"


def test_parse_args_requires_issues(iscs, tmp_path):
    """--issues is required."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        iscs.parse_args([
            "--lrm", str(lrm),
            "--organization", "o", "--repo", "r",
        ])


# ---- main -------------------------------------------------------------------


def _patch_main(monkeypatch, iscs):
    """Patch dependencies for main() and return mocks."""
    monkeypatch.setattr(
        iscs, "fetch_issue_title",
        lambda _o, _r, n: (
            f"Ensure IEEE 1800-2023 §6.{n - 99}"
            " functionalities and tests are implemented"
        ),
    )
    mock_invoke = MagicMock()
    monkeypatch.setattr(iscs, "invoke_implement_subclause", mock_invoke)
    return mock_invoke


def test_main_invokes_each_subclause(iscs, monkeypatch, base_argv):
    """main() invokes implement_subclause for each issue."""
    mock_invoke = _patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_count == 2


def test_main_passes_subclause(iscs, monkeypatch, base_argv):
    """main() passes the extracted subclause number."""
    mock_invoke = _patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[0][0][1] == "6.1"


def test_main_passes_issue_number(iscs, monkeypatch, base_argv):
    """main() passes the issue number."""
    mock_invoke = _patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[0][0][2] == 100


def test_main_second_uses_continue(iscs, monkeypatch, base_argv):
    """Second subclause uses continue_session=True."""
    mock_invoke = _patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[1][1]["continue_session"] is True


def test_main_first_no_continue(iscs, monkeypatch, base_argv):
    """First subclause does not use continue_session."""
    mock_invoke = _patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[0][1]["continue_session"] is False


def test_main_skips_unextractable_issue(iscs, monkeypatch, base_argv):
    """main() skips issues whose title has no subclause number."""
    monkeypatch.setattr(
        iscs, "fetch_issue_title",
        lambda _o, _r, _n: "Some unrelated issue title",
    )
    mock_invoke = MagicMock()
    monkeypatch.setattr(iscs, "invoke_implement_subclause", mock_invoke)
    iscs.main(base_argv)
    assert not mock_invoke.called


# ---- __main__ guard ---------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclauses", run_name="__main__")
