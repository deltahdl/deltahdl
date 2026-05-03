"""Stage, commit, and push the dependency-graph output file.

A long oracle walk takes hours; the ``--commit`` flag exists so that
the result is already saved to the remote when the walk finishes,
removing the risk of losing all that Claude work to a local disk
failure before a human gets back to commit by hand.

Failures are catastrophic by design: any unexpected git exit raises
``RuntimeError`` rather than being logged and ignored.
"""

import subprocess
from pathlib import Path


def _run(cmd: list[str]) -> subprocess.CompletedProcess:
    """Run *cmd* and return the completed process (no exceptions raised)."""
    return subprocess.run(cmd, check=False, capture_output=True, text=True)


def _ensure_clean_tree() -> None:
    """Raise if the working tree carries unstaged or untracked tracked changes."""
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


def _commit(path: Path) -> None:
    """Create the dependency-graph commit naming this script and *path*."""
    message = (
        f"document_dependency_graph: refresh {path}"
    )
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


def commit_output(path: Path) -> None:
    """Stage, commit, and push *path* as the only file in a new commit.

    Raises ``RuntimeError`` if the working tree is dirty before
    staging, or if any git step exits non-zero. Returns cleanly
    without committing when the staged diff is empty (the file
    already matches the last committed version).
    """
    _ensure_clean_tree()
    _stage(path)
    if not _has_staged_changes():
        return
    _commit(path)
    _push()
