"""Stage, commit, and push checkpoint writes of the dependency graph.

A long oracle walk takes hours; the ``--commit`` flag exists so that
each completed subclause is already saved to the remote when the walk
is interrupted, removing the risk of losing oracle work to a local
disk failure or a crash before a human gets back to commit by hand.

Failures are catastrophic by design: any unexpected git exit raises
``RuntimeError`` rather than being logged and ignored.
"""

import subprocess
from pathlib import Path


def _run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    """Run *cmd* and return the completed process (no exceptions raised)."""
    return subprocess.run(cmd, check=False, capture_output=True, text=True)


def assert_clean_tree() -> None:
    """Raise if the working tree carries unstaged or untracked tracked changes.

    Called once at startup before the walk begins so an unrelated dirty
    file does not race per-subclause checkpoint commits, and so the
    user sees the failure before any oracle calls happen.
    """
    proc = _run(["git", "status", "--porcelain", "--untracked-files=no"])
    if proc.stdout.strip():
        raise RuntimeError(
            "Refusing to commit: working tree has unrelated changes. "
            f"git status output:\n{proc.stdout}",
        )


def _stage(path: Path) -> None:
    """Stage *path* for the upcoming commit."""
    proc = _run(["git", "add", str(path)])
    if proc.returncode != 0:
        raise RuntimeError(
            f"git add {path} failed (exit {proc.returncode}): {proc.stderr}",
        )


def _has_staged_changes() -> bool:
    """Return True iff `git diff --cached` would show changes."""
    proc = _run(["git", "diff", "--cached", "--quiet"])
    return proc.returncode != 0


def _commit(message: str) -> None:
    """Create the dependency-graph commit with *message*."""
    proc = _run(["git", "commit", "-m", message])
    if proc.returncode != 0:
        raise RuntimeError(
            f"git commit failed (exit {proc.returncode}): {proc.stderr}",
        )


def _push() -> None:
    """Push the just-made commit to origin/main."""
    proc = _run(["git", "push", "origin", "main"])
    if proc.returncode != 0:
        raise RuntimeError(
            f"git push failed (exit {proc.returncode}): {proc.stderr}",
        )


def commit_output(path: Path, *, message: str) -> None:
    """Stage *path*, commit it with *message*, and push to origin/main.

    Returns cleanly without committing when the staged diff is empty
    (the file already matches the last committed version). Any
    non-zero git exit raises ``RuntimeError``.
    """
    _stage(path)
    if not _has_staged_changes():
        return
    _commit(message)
    _push()
