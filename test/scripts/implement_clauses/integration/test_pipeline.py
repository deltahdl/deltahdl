"""Integration tests for the implement_clauses pipeline."""

from pathlib import Path


SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


def _load(module_loader):
    """Load the implement_clauses module."""
    return module_loader(
        "implement_clauses",
        SCRIPTS_DIR / "implement_clauses" / "__init__.py",
    )


def _patch_externals(monkeypatch, icls):
    """Patch invoke_implement_clause and return call tracker."""
    calls = []

    def fake_invoke(lrm, clause, sub_issue, master, org, repo):
        calls.append((clause, sub_issue, master, org, repo))

    monkeypatch.setattr(icls, "invoke_implement_clause", fake_invoke)
    return calls


def test_pipeline_invokes_all_clauses(
    module_loader, monkeypatch, base_argv,
):
    """Full pipeline: parses args and invokes each clause."""
    icls = _load(module_loader)
    calls = _patch_externals(monkeypatch, icls)
    icls.main(base_argv)
    assert {c[0] for c in calls} == {"15", "16"}


def test_pipeline_passes_correct_sub_issues(
    module_loader, monkeypatch, base_argv,
):
    """Each clause is invoked with its matching sub-issue."""
    icls = _load(module_loader)
    calls = _patch_externals(monkeypatch, icls)
    icls.main(base_argv)
    assert {c[0]: c[1] for c in calls} == {"15": 17, "16": 18}
