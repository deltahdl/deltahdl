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
        orig = getattr(t, "original_test_name", None)
        lookup_name = orig or t.test_name
        renamed = orig is not None and orig != t.test_name
        parts = []
        if source_is_target:
            parts.append("Kept in the same file")
        elif target_filenames:
            fname = target_filenames.get(t.test_name, "")
            if fname:
                parts.append(f"Moved to {fname}")
        if renamed:
            parts.append(f"renamed to {t.test_name}")
        if len(parts) == 2:
            joiner = " but " if source_is_target else " and "
            remark = parts[0] + joiner + parts[1]
        elif parts:
            remark = parts[0]
        else:
            remark = ""
        body = update_test_status(
            body, lookup_name, status, remark=remark,
        )
    print(f"Updating status to '{status}' for issue #{args.issue}...")
    update_issue_body(
        args.organization, args.repo, args.issue, body,
    )
