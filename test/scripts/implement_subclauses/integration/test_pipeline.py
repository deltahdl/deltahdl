"""Integration tests for the implement_subclauses pipeline."""

from pathlib import Path
from unittest.mock import MagicMock


SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


def _load(module_loader):
    """Load the implement_subclauses module."""
    return module_loader(
        "implement_subclauses",
        SCRIPTS_DIR / "implement_subclauses" / "__init__.py",
    )


def _patch_externals(monkeypatch, iscs):
    """Patch fetch_issue_title and invoke_implement_subclause."""
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


def test_pipeline_invokes_each_issue(
    module_loader, monkeypatch, base_argv,
):
    """Full pipeline: parses args, fetches titles, invokes per subclause."""
    iscs = _load(module_loader)
    mock_invoke = _patch_externals(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_count == 2


def test_pipeline_continue_session_progression(
    module_loader, monkeypatch, base_argv,
):
    """First subclause has continue=False, second has continue=True."""
    iscs = _load(module_loader)
    mock_invoke = _patch_externals(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[0][1]["continue_session"] is False
    assert mock_invoke.call_args_list[1][1]["continue_session"] is True
