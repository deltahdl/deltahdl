"""Unit tests for satisfy_subclause.pipeline._list_issues_for.

The §X master-list / legacy-audit issues for a heavily-subdivided clause
(e.g. §23, with §23.x.y.z descendants) easily exceed the 30-result default
of ``gh issue list``. If the gh invocation does not raise that limit, the
master-list issue (e.g. #25 for §23) ends up past the cutoff and the
matcher silently opens a duplicate (#1290 vs #25 — see issue #1278).

These tests guard the limit by inspecting the gh argv.
"""

from unittest.mock import patch

from satisfy_subclause.pipeline import _list_issues_for


def _gh_argv_for(stub_completed) -> list[str]:
    """Run _list_issues_for with a stubbed gh and return its argv."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(stdout="[]"),
    ) as mock_run:
        _list_issues_for("23")
    return mock_run.call_args_list[0][0][0]


def test_list_issues_for_passes_limit_flag(stub_completed) -> None:
    """_list_issues_for invokes gh with an explicit --limit flag."""
    assert "--limit" in _gh_argv_for(stub_completed)


def test_list_issues_for_limit_value_clears_real_clause_count(
    stub_completed,
) -> None:
    """The --limit value comfortably exceeds the worst-case §X result count.

    §23 alone returns ~46 entries today and the matcher must see all of
    them. 1000 is the floor we commit to.
    """
    argv = _gh_argv_for(stub_completed)
    limit = int(argv[argv.index("--limit") + 1])
    assert limit >= 1000
