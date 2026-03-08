"""Shared git commit and push helpers."""

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
    """Stage changed/deleted files, commit with message, and push."""
    if not changed_files and not deleted_files:
        return
    for f in changed_files:
        run_git(["git", "add", str(f)])
    for f in deleted_files:
        run_git(["git", "rm", str(f)])
    print("Committing...")
    run_git(["git", "commit", "-F", "-"], input=message)
    print("Committed.")
    print("Pushing...")
    run_git(["git", "push"])
    print("Pushed.")
