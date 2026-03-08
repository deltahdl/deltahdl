"""Integration tests for the implement_subclauses pipeline."""

from pathlib import Path


SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


def _load(module_loader):
    """Load the implement_subclauses module."""
    return module_loader(
        "implement_subclauses",
        SCRIPTS_DIR / "implement_subclauses" / "__init__.py",
    )


def _patch_externals(monkeypatch, iscs, patch_completion, *, all_complete=True):
    """Patch subprocess and GitHub calls, return call trackers."""
    calls = []

    def fake_invoke(_lrm, sub, _issue, _model, cont):
        calls.append(("invoke", sub, cont))

    monkeypatch.setattr(iscs, "invoke_implement_subclause", fake_invoke)

    patch_completion(monkeypatch, iscs, all_complete=all_complete)

    close_calls = []
    monkeypatch.setattr(
        iscs, "close_issue",
        lambda *a: close_calls.append(a),
    )

    mark_calls = []
    monkeypatch.setattr(
        iscs, "mark_master_complete",
        lambda *a: mark_calls.append(a),
    )

    return calls, close_calls, mark_calls


def test_pipeline_invokes_then_closes(
    module_loader, monkeypatch, base_argv, patch_completion,
):
    """Full pipeline: parses args, invokes subclauses, closes issue."""
    iscs = _load(module_loader)
    calls, _, __ = _patch_externals(
        monkeypatch, iscs, patch_completion, all_complete=True,
    )
    iscs.main(base_argv)
    assert [c[1] for c in calls] == ["6.1", "6.2"]


def test_pipeline_continue_session_progression(
    module_loader, monkeypatch, base_argv, patch_completion,
):
    """First subclause has continue=False, second has continue=True."""
    iscs = _load(module_loader)
    calls, _, __ = _patch_externals(
        monkeypatch, iscs, patch_completion, all_complete=True,
    )
    iscs.main(base_argv)
    assert [c[2] for c in calls] == [False, True]


def test_pipeline_closes_when_all_complete(
    module_loader, monkeypatch, base_argv, patch_completion,
):
    """Issue is closed when all subclauses are complete."""
    iscs = _load(module_loader)
    _, close_calls, __ = _patch_externals(
        monkeypatch, iscs, patch_completion, all_complete=True,
    )
    iscs.main(base_argv)
    assert len(close_calls) == 1


def test_pipeline_marks_master_when_all_complete(
    module_loader, monkeypatch, base_argv, patch_completion,
):
    """Master issue is marked when all subclauses are complete."""
    iscs = _load(module_loader)
    _, __, mark_calls = _patch_externals(
        monkeypatch, iscs, patch_completion, all_complete=True,
    )
    iscs.main(base_argv)
    assert len(mark_calls) == 1


def test_pipeline_skips_close_when_incomplete(
    module_loader, monkeypatch, base_argv, patch_completion,
):
    """Issue is not closed when subclauses remain."""
    iscs = _load(module_loader)
    _, close_calls, __ = _patch_externals(
        monkeypatch, iscs, patch_completion, all_complete=False,
    )
    iscs.main(base_argv)
    assert not close_calls


def test_pipeline_skips_mark_when_incomplete(
    module_loader, monkeypatch, base_argv, patch_completion,
):
    """Master issue is not marked when subclauses remain."""
    iscs = _load(module_loader)
    _, __, mark_calls = _patch_externals(
        monkeypatch, iscs, patch_completion, all_complete=False,
    )
    iscs.main(base_argv)
    assert not mark_calls
