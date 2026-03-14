"""Integration tests for the implement_subclauses pipeline."""

from pathlib import Path


SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


def _load(module_loader):
    """Load the implement_subclauses module."""
    return module_loader(
        "implement_subclauses",
        SCRIPTS_DIR / "implement_subclauses" / "__init__.py",
    )


def test_pipeline_invokes_each_issue(
    module_loader, monkeypatch, base_argv, patch_main,
):
    """Full pipeline: parses args, fetches titles, invokes per subclause."""
    iscs = _load(module_loader)
    mock_invoke = patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_count == 2


def test_pipeline_first_no_continue(
    module_loader, monkeypatch, base_argv, patch_main,
):
    """First subclause has continue_session=False."""
    iscs = _load(module_loader)
    mock_invoke = patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[0][1]["continue_session"] is False


def test_pipeline_second_uses_continue(
    module_loader, monkeypatch, base_argv, patch_main,
):
    """Second subclause has continue_session=True."""
    iscs = _load(module_loader)
    mock_invoke = patch_main(monkeypatch, iscs)
    iscs.main(base_argv)
    assert mock_invoke.call_args_list[1][1]["continue_session"] is True
