"""Git commit and push integration for classify_test."""

import subprocess
import sys

from classify_test._output import _format_clause


def build_commit_message(test_name, clause, rationale):
    """Build a classify_test commit message.

    Format:
        Classify <TestName> → §<clause> [skip ci]

        <rationale>

        Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
    """
    title = f"Classify {test_name} → {_format_clause(clause)} [skip ci]"
    trailer = "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    return f"{title}\n\n{rationale}\n\n{trailer}\n"


def _run_git(cmd, **kwargs):
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
        _run_git(["git", "add", str(f)])
    for f in deleted_files:
        _run_git(["git", "rm", str(f)])
    _run_git(["git", "commit", "-F", "-"], input=message)
    _run_git(["git", "push"])
    print("Committed and pushed")


def commit_classification(ctx):
    """Build file lists and commit+push the classification result.

    *ctx* is a dict with keys: filepath, target, to_merge, new_names,
    test_dir, cmake_path.
    """
    filepath = ctx["filepath"]
    changed = [ctx["test_dir"] / f"{n}.cpp" for n in ctx["new_names"]]
    changed.extend(mp for mp, _ in ctx["to_merge"])
    changed.append(ctx["cmake_path"])
    deleted = []
    if filepath.exists():
        changed.append(filepath)
    else:
        deleted.append(filepath)
    t = ctx["target"][0]
    msg = build_commit_message(t.test_name, t.clause, t.rationale)
    commit_and_push(changed, deleted, msg)
