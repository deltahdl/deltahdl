"""GitHub issue integration for classify_test."""

import subprocess
import sys

from ._output import _format_clause


def _validate_issue_args(args):
    """Validate that --organization and --repo are present when --issue is."""
    if args.issue and not args.organization:
        print("ERROR: --organization is required when"
              " --issue is provided")
        sys.exit(1)
    if args.issue and not args.repo:
        print("ERROR: --repo is required when"
              " --issue is provided")
        sys.exit(1)


def build_issue_comment(tests):
    """Build markdown comment body for GitHub issue."""
    lines = ["### Test Classification Results", ""]
    for t in tests:
        clause_display = _format_clause(t.clause)
        lines.append(f"- **{t.test_name}()** \u2192 {clause_display}")
        if t.rationale:
            lines.append(f"  - {t.rationale}")
    return "\n".join(lines)


def post_issue_comment(organization, repo, issue, body):
    """Post a comment on a GitHub issue using gh CLI."""
    result = subprocess.run(
        ["gh", "issue", "comment", str(issue),
         "--repo", f"{organization}/{repo}",
         "--body", body],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to post comment to issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)


def maybe_post_issue_comment(args, tests):
    """Post a classification comment to a GitHub issue if --issue is set."""
    if not args.issue:
        return
    comment = build_issue_comment(tests)
    post_issue_comment(
        args.organization, args.repo,
        args.issue, comment,
    )
