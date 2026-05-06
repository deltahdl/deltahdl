"""Unit tests for generate_lrm_subclause_dependencies.commit (the --commit path)."""

from collections.abc import Callable
from pathlib import Path


def test_commit_runs_git_add(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """commit_output stages the output file."""
    cmds, _, out = run_commit()
    assert any(c.startswith(f"git add {out}") for c in cmds)


def test_commit_uses_supplied_message(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """commit_output passes the caller's message verbatim to git commit."""
    cmds, _, _ = run_commit(message="custom-checkpoint-token")
    assert any(
        "git commit" in c and "custom-checkpoint-token" in c for c in cmds
    )


def test_commit_runs_git_push(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """commit_output pushes after committing."""
    cmds, _, _ = run_commit()
    assert any("git push" in c for c in cmds)


def test_commit_skips_when_no_diff(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """No commit + no push if the staged diff is empty."""
    cmds, _, _ = run_commit(staged_diff=False)
    assert not any(c.startswith("git commit") for c in cmds)


def test_commit_crashes_on_add_failure(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """A non-zero git add exit raises RuntimeError."""
    _, raised, _ = run_commit(git_add_rc=128)
    assert isinstance(raised, RuntimeError)


def test_commit_crashes_on_commit_failure(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """A non-zero git commit exit raises RuntimeError."""
    _, raised, _ = run_commit(git_commit_rc=128)
    assert isinstance(raised, RuntimeError)


def test_commit_crashes_on_push_failure(
    run_commit: Callable[..., tuple[list[str], RuntimeError | None, Path]],
) -> None:
    """A non-zero git push exit raises RuntimeError."""
    _, raised, _ = run_commit(git_push_rc=128)
    assert isinstance(raised, RuntimeError)


def test_assert_clean_tree_passes_when_clean(
    run_assert_clean_tree: Callable[..., RuntimeError | None],
) -> None:
    """A clean working tree returns without raising."""
    raised = run_assert_clean_tree(dirty=False)
    assert raised is None


def test_assert_clean_tree_raises_when_dirty(
    run_assert_clean_tree: Callable[..., RuntimeError | None],
) -> None:
    """A dirty working tree raises RuntimeError."""
    raised = run_assert_clean_tree(dirty=True)
    assert isinstance(raised, RuntimeError)
