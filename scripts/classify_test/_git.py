"""Git commit and push integration for classify_test."""

from classify_test._output import _format_clause
from lib.python.git import commit_and_push, run_git

# Re-export for backwards compatibility within classify_test.
_run_git = run_git


def build_commit_message(test_name, clause, rationale, action=""):
    """Build a classify_test commit message.

    Format:
        Classify <TestName> → §<clause> [skip ci]

        <rationale>

        Action: <action>

        Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
    """
    title = f"Classify {test_name} → {_format_clause(clause)} [skip ci]"
    trailer = "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    body = rationale
    if action:
        body = f"{rationale}\n\nAction: {action}"
    return f"{title}\n\n{body}\n\n{trailer}\n"


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
    action = ctx.get("action", "")
    msg = build_commit_message(t.test_name, t.clause, t.rationale, action)
    return commit_and_push(changed, deleted, msg)
