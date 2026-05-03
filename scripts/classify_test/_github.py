"""GitHub issue integration for classify_test."""

import argparse
import re
import sys
from typing import Any

from lib.python.github import fetch_issue_body, update_issue_body


def _validate_issue_args(args: argparse.Namespace) -> None:
    """Validate that --organization and --repo are present when --issue is."""
    if args.issue and not args.organization:
        print("ERROR: --organization is required when"
              " --issue is provided")
        sys.exit(1)
    if args.issue and not args.repo:
        print("ERROR: --repo is required when"
              " --issue is provided")
        sys.exit(1)


def update_test_status(
    body: str, test_name: str, status: str, *, remark: str = "",
) -> str:
    """Update the Status column for test_name in the issue table."""
    row_re = re.compile(
        r"^(\|[^|]*)\| " + re.escape(test_name) + r" \|[^|]*\|[^|]*\|$",
        re.MULTILINE,
    )
    match = row_re.search(body)
    if not match:
        print(f"ERROR: Row for {test_name!r} not found in issue body")
        sys.exit(1)
    remark_cell = f" {remark} " if remark else " "
    new_row = f"{match.group(1)}| {test_name} | {status} |{remark_cell}|"
    return body[:match.start()] + new_row + body[match.end():]


def build_action_remark(
    test: Any,
    *,
    source_is_target: bool,
    target_filename: str | None = None,
    commit_url: str = "",
) -> str:
    """Build a human-readable action remark for a classified test."""
    orig_test = test.classification.original_test_name
    test_renamed = orig_test is not None and orig_test != test.test_name
    orig_suite = test.classification.original_suite_name
    suite_renamed = (
        orig_suite is not None and orig_suite != test.suite_name
    )
    location = ""
    if source_is_target:
        if not test_renamed and not suite_renamed:
            return "Kept in the same file without any changes"
        location = "Kept in the same file"
    elif target_filename:
        location = f"Moved to {target_filename}"
    if suite_renamed and test_renamed:
        rename_str = (f"renamed suite to {test.suite_name}"
                      f" and test to {test.test_name}")
    elif suite_renamed:
        rename_str = f"renamed suite to {test.suite_name}"
    elif test_renamed:
        rename_str = f"renamed test to {test.test_name}"
    else:
        rename_str = ""
    if location and rename_str:
        joiner = " but " if source_is_target else " and "
        remark = location + joiner + rename_str
    elif location:
        remark = location
    else:
        remark = rename_str
    if commit_url and remark:
        return f"[{remark}]({commit_url})"
    return remark


def maybe_update_issue_status(
    args: argparse.Namespace,
    tests: list[Any],
    *,
    source_is_target: bool,
    target_filenames: dict[str, str] | None = None,
    commit_url: str = "",
) -> None:
    """Update status for classified tests in a GitHub issue."""
    if args.issue is None:
        return
    status = "Reviewed"
    print(f"Fetching issue #{args.issue}...")
    body = fetch_issue_body(
        args.organization, args.repo, args.issue,
    )
    for t in tests:
        lookup_name = t.classification.original_test_name or t.test_name
        fname = (target_filenames or {}).get(t.test_name, "")
        remark = build_action_remark(
            t,
            source_is_target=source_is_target,
            target_filename=fname,
            commit_url=commit_url,
        )
        body = update_test_status(
            body, lookup_name, status, remark=remark,
        )
    print(f"Updating status to '{status}' for issue #{args.issue}...")
    update_issue_body(
        args.organization, args.repo, args.issue, body,
    )


def build_commit_url(args: argparse.Namespace, sha: str | None) -> str:
    """Build a GitHub commit URL from org/repo and SHA."""
    if not sha:
        return ""
    return (f"https://github.com/{args.organization}"
            f"/{args.repo}/commit/{sha}")


def update_issue_after_commit(
    args: argparse.Namespace,
    target: list[Any],
    source_is_target: bool,
    target_filenames: dict[str, str] | None,
    commit_url: str = "",
) -> None:
    """Update the GitHub issue with the action and commit link."""
    if args.issue is None:
        return
    maybe_update_issue_status(
        args, target,
        source_is_target=source_is_target,
        target_filenames=target_filenames,
        commit_url=commit_url,
    )
