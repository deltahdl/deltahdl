"""Shared git commit and push helpers."""

import subprocess
import sys
from typing import Any


def run_git(cmd: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
    """Run a git command and exit on failure."""
    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        **kwargs,
    )
    if result.returncode != 0:
        print(f"ERROR: {' '.join(cmd[:2])} failed"
              f" (RC={result.returncode}):"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result


def commit_and_push(
    changed_files: list[str],
    deleted_files: list[str],
    message: str,
) -> str | None:
    """Stage changed/deleted files, commit with message, and push.

    Returns the commit SHA on success, or ``None`` when there is nothing
    to commit.
    """
    if not changed_files and not deleted_files:
        return None
    for f in changed_files:
        run_git(["git", "add", str(f)])
    for f in deleted_files:
        run_git(["git", "rm", str(f)])
    print("Committing...")
    run_git(["git", "commit", "-F", "-"], input=message)
    result = run_git(["git", "rev-parse", "HEAD"])
    sha = result.stdout.strip()
    print("Committed.")
    print("Pushing...")
    run_git(["git", "push"])
    print("Pushed.")
    return sha


def get_porcelain_changes() -> tuple[list[str], list[str], list[str]]:
    """Return (added, modified, deleted) from ``git status --porcelain``."""
    result = run_git(["git", "status", "--porcelain"])
    added: list[str] = []
    modified: list[str] = []
    deleted: list[str] = []
    for line in result.stdout.splitlines():
        if not line:
            continue
        status = line[:2]
        path = line[3:]
        if status == "??":
            added.append(path)
        elif status.strip() == "D":
            deleted.append(path)
        else:
            modified.append(path)
    return added, modified, deleted
