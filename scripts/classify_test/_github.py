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


def _checkbox_patterns(test_name):
    """Return (unchecked, checked) regexes for plain or linked checkbox."""
    escaped = re.escape(test_name)
    suffix = r"(?:\[" + escaped + r"\]\([^)]*\)|" + escaped + r")"
    unchecked = re.compile(
        r"^(- \[) \] " + suffix + r"$", re.MULTILINE,
    )
    checked = re.compile(
        r"^- \[x\] " + suffix + r"$", re.MULTILINE,
    )
    return unchecked, checked


def tick_checkbox(body, test_name):
    """Replace '- [ ] test_name' with '- [x] test_name' in body."""
    unchecked, checked = _checkbox_patterns(test_name)
    match = unchecked.search(body)
    if not match:
        if checked.search(body):
            return body
        print(f"ERROR: Checkbox for {test_name!r} not found"
              " in issue body")
        sys.exit(1)
    line = match.group(0)
    ticked = line[:len("- [")] + "x" + line[len("- [x"):]
    return body[:match.start()] + ticked + body[match.end():]


def remove_checkbox(body, test_name):
    """Remove the checkbox line for test_name from body."""
    escaped = re.escape(test_name)
    suffix = r"(?:\[" + escaped + r"\]\([^)]*\)|" + escaped + r")"
    pattern = re.compile(
        r"^- \[[ x]\] " + suffix + r"\n?", re.MULTILINE,
    )
    match = pattern.search(body)
    if not match:
        raise ValueError(
            f"Checkbox for {test_name!r} not found in issue body",
        )
    return body[:match.start()] + body[match.end():]


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
    print(f"Fetching issue #{args.issue}...")
    body = fetch_issue_body(
        args.organization, args.repo, args.issue,
    )
    for t in tests:
        body = tick_checkbox(body, t.test_name)
    print(f"Ticking checkbox for issue #{args.issue}...")
    update_issue_body(
        args.organization, args.repo, args.issue, body,
    )
