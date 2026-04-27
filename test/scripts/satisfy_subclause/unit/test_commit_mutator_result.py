"""Unit tests for satisfy_subclause.mutators.commit_mutator_result.

Covers the porcelain-to-commit pipeline: clean-tree close-issue
fallback, dirty-tree commit-and-push flow, garbage filtering,
generate_commit_body invocation, and the porcelain-derived bullet-list
fallback when Claude returns a blank body.
"""

from unittest.mock import patch

import pytest

from satisfy_subclause.mutators import commit_mutator_result


def _patched_porcelain(changes):
    """Patch get_porcelain_changes with a fixed return value."""
    return patch(
        "satisfy_subclause.mutators.get_porcelain_changes",
        return_value=changes,
    )


def _patched_commit():
    """Patch commit_and_push with a no-op MagicMock."""
    return patch(
        "satisfy_subclause.mutators.commit_and_push",
        return_value="abc123",
    )


def _patched_close():
    """Patch the gh-issue-close subprocess shim."""
    return patch("satisfy_subclause.mutators._close_satisfied_issue")


def _patched_body(value: str = ""):
    """Patch generate_commit_body to return *value* (default: empty fallback)."""
    return patch(
        "satisfy_subclause.mutators.generate_commit_body",
        return_value=value,
    )


@pytest.mark.parametrize(
    "porcelain", [([], [], []), (["{a,"], [], [])],
    ids=["clean", "only-garbage"],
)
def test_commit_mutator_result_returns_false_when_no_committable(
    porcelain,
) -> None:
    """A clean tree (or one filtered down to empty) returns False."""
    with _patched_porcelain(porcelain), _patched_commit() as mock_c, \
            _patched_close(), _patched_body():
        result = commit_mutator_result(["6.3"], [42], model="opus")
    assert (result, mock_c.called) == (False, False)


def test_commit_mutator_result_returns_true_when_dirty() -> None:
    """commit_mutator_result returns True when porcelain has source files."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit(), \
            _patched_close(), _patched_body():
        result = commit_mutator_result(["6.3"], [42], model="opus")
    assert result is True


def test_commit_mutator_result_calls_commit_and_push() -> None:
    """commit_mutator_result invokes commit_and_push with the file list."""
    with _patched_porcelain((["foo.cpp"], ["bar.h"], [])), \
            _patched_commit() as mock_c, _patched_close(), _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_c.call_args[0][0] == ["foo.cpp", "bar.h"]


def test_commit_mutator_result_filters_garbage_added() -> None:
    """commit_mutator_result drops garbage paths from added before commit."""
    with _patched_porcelain((["foo.cpp", "{a,"], [], [])), \
            _patched_commit() as mock_c, _patched_close(), _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_c.call_args[0][0] == ["foo.cpp"]


def test_commit_mutator_result_filters_garbage_deleted() -> None:
    """commit_mutator_result drops garbage paths from deleted before commit."""
    with _patched_porcelain(([], [], ["foo.cpp", "{a,"])), \
            _patched_commit() as mock_c, _patched_close(), _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_c.call_args[0][1] == ["foo.cpp"]


@pytest.mark.parametrize(
    "porcelain", [([], [], []), (["{a,"], [], [])],
    ids=["clean", "only-garbage"],
)
def test_commit_mutator_result_closes_issue_when_no_committable(
    porcelain,
) -> None:
    """A clean (or filter-empty) tree means §X is satisfied → issue is closed."""
    with _patched_porcelain(porcelain), _patched_commit(), \
            _patched_close() as mock_close, _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_close.call_args[0] == ("6.3", 42)


def test_commit_mutator_result_closes_every_issue_in_cycle() -> None:
    """A clean tree closes every (subclause, issue) pair in a cycle set."""
    with _patched_porcelain(([], [], [])), _patched_commit(), \
            _patched_close() as mock_close, _patched_body():
        commit_mutator_result(["6.3", "6.4"], [42, 43], model="opus")
    pairs = [call.args for call in mock_close.call_args_list]
    assert pairs == [("6.3", 42), ("6.4", 43)]


def test_commit_mutator_result_skips_close_when_committing() -> None:
    """When a commit is produced, the gh-close fallback is not invoked."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit(), \
            _patched_close() as mock_close, _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_close.called is False


def test_commit_mutator_result_only_deletions_commits() -> None:
    """A commit composed solely of deletions still commits."""
    with _patched_porcelain(([], [], ["foo.cpp"])), \
            _patched_commit() as mock_c, _patched_body():
        result = commit_mutator_result(["6.3"], [42], model="opus")
    assert (result, mock_c.called) == (True, True)


def test_commit_mutator_result_summary_lists_added() -> None:
    """The commit summary lists added files when the body generator is blank."""
    with _patched_porcelain((["foo.cpp"], [], [])), \
            _patched_commit() as mock_c, _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    message = mock_c.call_args[0][2]
    assert "Added foo.cpp" in message


def test_commit_mutator_result_summary_lists_modified() -> None:
    """The commit summary lists modified files when the body generator is blank."""
    with _patched_porcelain(([], ["bar.h"], [])), \
            _patched_commit() as mock_c, _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    message = mock_c.call_args[0][2]
    assert "Modified bar.h" in message


def test_commit_mutator_result_summary_lists_deleted() -> None:
    """The commit summary lists deleted files when the body generator is blank."""
    with _patched_porcelain(([], [], ["baz.py"])), \
            _patched_commit() as mock_c, _patched_close(), _patched_body():
        commit_mutator_result(["6.3"], [42], model="opus")
    message = mock_c.call_args[0][2]
    assert "Deleted baz.py" in message


def test_commit_mutator_result_uses_claude_body_when_present() -> None:
    """A non-blank generate_commit_body result goes verbatim into the message."""
    with _patched_porcelain((["foo.cpp"], [], [])), \
            _patched_commit() as mock_c, _patched_close(), \
            _patched_body("- Added `foo.cpp` because reasons."):
        commit_mutator_result(["6.3"], [42], model="opus")
    message = mock_c.call_args[0][2]
    assert "- Added `foo.cpp` because reasons." in message


def test_commit_mutator_result_invokes_generate_commit_body() -> None:
    """Source-tree changes trigger a generate_commit_body call."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit(), \
            _patched_close(), _patched_body() as mock_body:
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_body.called is True


def test_commit_mutator_result_skips_body_call_when_clean() -> None:
    """A clean tree never calls the body generator."""
    with _patched_porcelain(([], [], [])), _patched_commit(), \
            _patched_close(), _patched_body() as mock_body:
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_body.called is False


def test_commit_mutator_result_passes_model_to_body() -> None:
    """The model argument flows through to generate_commit_body."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit(), \
            _patched_close(), _patched_body() as mock_body:
        commit_mutator_result(["6.3"], [42], model="haiku")
    assert mock_body.call_args[1]["model"] == "haiku"


def test_commit_mutator_result_passes_subclauses_to_body() -> None:
    """generate_commit_body sees the subclause list."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit(), \
            _patched_close(), _patched_body() as mock_body:
        commit_mutator_result(["6.3"], [42], model="opus")
    assert mock_body.call_args[0][0] == ["6.3"]


def test_commit_mutator_result_passes_filtered_changes_to_body() -> None:
    """generate_commit_body receives the porcelain lists post-filter."""
    with _patched_porcelain((["foo.cpp", "{a,"], ["bar.h"], ["baz.py"])), \
            _patched_commit(), _patched_close(), _patched_body() as mock_body:
        commit_mutator_result(["6.3"], [42], model="opus")
    args = mock_body.call_args[0]
    assert (args[1], args[2], args[3]) == (
        ["foo.cpp"], ["bar.h"], ["baz.py"],
    )
