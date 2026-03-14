"""Shared git commit and push helpers."""

import os.path
import re
import subprocess
import sys


def run_git(cmd, **kwargs):
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


def commit_and_push(changed_files, deleted_files, message):
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


_REMOTE_RE = re.compile(
    r"(?:git@github\.com:|https://github\.com/)([^/]+)/([^/]+?)(?:\.git)?$",
)


def get_remote_repo(remote: str = "origin") -> tuple[str, str]:
    """Return ``(organization, repo)`` parsed from the git remote URL."""
    result = run_git(["git", "remote", "get-url", remote])
    url = result.stdout.strip()
    m = _REMOTE_RE.match(url)
    if not m:
        print(f"ERROR: Cannot parse org/repo from remote URL: {url}",
              file=sys.stderr)
        sys.exit(1)
    return m.group(1), m.group(2)


def get_porcelain_changes():
    """Return (added, modified, deleted) from ``git status --porcelain``."""
    result = run_git(["git", "status", "--porcelain"])
    added, modified, deleted = [], [], []
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


def build_file_change_summary(added, modified, deleted):
    """Build a human-readable summary of file changes.

    Returns a string like ``"Added foo.cpp, bar.cpp; modified baz.cpp;
    deleted old.cpp"`` using basenames sorted alphabetically.  Returns
    ``""`` when all lists are empty.
    """
    parts = []
    for label, files in [("Added", added), ("modified", modified),
                         ("deleted", deleted)]:
        if files:
            names = sorted(os.path.basename(f) for f in files)
            parts.append(f"{label} {', '.join(names)}")
    return "; ".join(parts)
