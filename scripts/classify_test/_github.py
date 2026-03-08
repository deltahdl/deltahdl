"""GitHub issue integration for classify_test."""

import re
import sys

from lib.python.github import fetch_issue_body, update_issue_body


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


def update_test_status(body, test_name, status, *, remark=""):
    """Update the Status column for test_name in the issue table."""
    row_re = re.compile(
        r"^\| " + re.escape(test_name) + r" \|[^|]*\|[^|]*\|$",
        re.MULTILINE,
    )
    match = row_re.search(body)
    if not match:
        print(f"ERROR: Row for {test_name!r} not found in issue body")
        sys.exit(1)
    remark_cell = f" {remark} " if remark else " "
    new_row = f"| {test_name} | {status} |{remark_cell}|"
    return body[:match.start()] + new_row + body[match.end():]


def maybe_update_issue_status(
    args, tests, *, source_is_target, target_filenames=None,
):
    """Update status for classified tests in a GitHub issue."""
    status = "Reviewed"
    print(f"Fetching issue #{args.issue}...")
    body = fetch_issue_body(
        args.organization, args.repo, args.issue,
    )
    for t in tests:
        if source_is_target:
            remark = "Kept in the same file"
        elif target_filenames:
            fname = target_filenames.get(t.test_name, "")
            remark = f"Moved to {fname}" if fname else ""
        else:
            remark = ""
        body = update_test_status(
            body, t.test_name, status, remark=remark,
        )
    print(f"Updating status to '{status}' for issue #{args.issue}...")
    update_issue_body(
        args.organization, args.repo, args.issue, body,
    )
