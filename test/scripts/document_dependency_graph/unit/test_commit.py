"""Unit tests for document_dependency_graph.commit (the --commit path)."""


def test_commit_runs_git_add(run_commit) -> None:
    """commit_output stages the output file."""
    cmds, _, out = run_commit()
    assert any(c.startswith(f"git add {out}") for c in cmds)


def test_commit_runs_git_commit(run_commit) -> None:
    """commit_output creates a commit naming the script and the path."""
    cmds, _, out = run_commit()
    assert any(
        "git commit" in c
        and "document_dependency_graph" in c
        and str(out) in c
        for c in cmds
    )


def test_commit_runs_git_push(run_commit) -> None:
    """commit_output pushes after committing."""
    cmds, _, _ = run_commit()
    assert any("git push" in c for c in cmds)


def test_commit_skips_when_no_diff(run_commit) -> None:
    """No commit + no push if the staged diff is empty."""
    cmds, _, _ = run_commit(staged_diff=False)
    assert not any(c.startswith("git commit") for c in cmds)


def test_commit_aborts_on_dirty_tree(run_commit) -> None:
    """A dirty working tree raises RuntimeError."""
    _, raised, _ = run_commit(dirty=True)
    assert isinstance(raised, RuntimeError)


def test_commit_dirty_tree_does_not_stage(run_commit) -> None:
    """A dirty working tree raises without ever running git add."""
    cmds, _, _ = run_commit(dirty=True)
    assert not any(c.startswith("git add") for c in cmds)


def test_commit_crashes_on_add_failure(run_commit) -> None:
    """A non-zero git add exit raises RuntimeError."""
    _, raised, _ = run_commit(git_add_rc=128)
    assert isinstance(raised, RuntimeError)


def test_commit_crashes_on_commit_failure(run_commit) -> None:
    """A non-zero git commit exit raises RuntimeError."""
    _, raised, _ = run_commit(git_commit_rc=128)
    assert isinstance(raised, RuntimeError)


def test_commit_crashes_on_push_failure(run_commit) -> None:
    """A non-zero git push exit raises RuntimeError."""
    _, raised, _ = run_commit(git_push_rc=128)
    assert isinstance(raised, RuntimeError)
