import subprocess
from pathlib import Path


def _run(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, check=False, capture_output=True, text=True)


def assert_clean_tree() -> None:
    proc = _run(["git", "status", "--porcelain", "--untracked-files=no"])
    if proc.stdout.strip():
        raise RuntimeError(
            "Refusing to commit: working tree has unrelated changes. "
            f"git status output:\n{proc.stdout}",
        )


def _stage(path: Path) -> None:
    proc = _run(["git", "add", str(path)])
    if proc.returncode != 0:
        raise RuntimeError(
            f"git add {path} failed (exit {proc.returncode}): {proc.stderr}",
        )


def _has_staged_changes() -> bool:
    proc = _run(["git", "diff", "--cached", "--quiet"])
    return proc.returncode != 0


def _commit(message: str) -> None:
    proc = _run(["git", "commit", "-m", message])
    if proc.returncode != 0:
        raise RuntimeError(
            f"git commit failed (exit {proc.returncode}): {proc.stderr}",
        )


def _push() -> None:
    proc = _run(["git", "push", "origin", "main"])
    if proc.returncode != 0:
        raise RuntimeError(
            f"git push failed (exit {proc.returncode}): {proc.stderr}",
        )


def commit_output(path: Path, *, message: str) -> None:
    _stage(path)
    if not _has_staged_changes():
        return
    _commit(message)
    _push()
