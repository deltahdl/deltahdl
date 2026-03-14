"""Shared git commit and push helpers."""

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
