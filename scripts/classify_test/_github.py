"""GitHub issue integration for classify_test."""

import json
import re
import subprocess
import sys


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


def tick_checkbox(body, test_name):
    """Replace '- [ ] test_name' with '- [x] test_name' in body."""
    pattern = re.compile(
        r"^(- \[) \] " + re.escape(test_name) + r"$",
        re.MULTILINE,
    )
    if not pattern.search(body):
        if re.search(
            r"^- \[x\] " + re.escape(test_name) + r"$",
            body, re.MULTILINE,
        ):
            return body
        print(f"ERROR: Checkbox for {test_name!r} not found"
              " in issue body")
        sys.exit(1)
    return pattern.sub(r"\1x] " + test_name, body)


def fetch_issue_body(organization, repo, issue):
    """Fetch the body of a GitHub issue using gh api."""
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "--jq", ".body"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to fetch issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout


def update_issue_body(organization, repo, issue, body):
    """Update the body of a GitHub issue using gh api."""
    payload = json.dumps({"body": body})
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "-X", "PATCH", "--input", "-"],
        input=payload,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to update issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)


def maybe_tick_issue_checkbox(args, tests):
    """Tick checkboxes for classified tests in a GitHub issue."""
    body = fetch_issue_body(
        args.organization, args.repo, args.issue,
    )
    for t in tests:
        body = tick_checkbox(body, t.test_name)
    update_issue_body(
        args.organization, args.repo, args.issue, body,
    )
