"""Batch wrapper around implement_subclause for multiple subclauses.

Loops through issue numbers, fetches each issue title to extract the
subclause number, and invokes implement_subclause for each one.
"""

import argparse

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    invoke_implement_subclause,
    parse_and_validate,
)
from lib.python.github import (
    extract_subclause_from_title,
    fetch_issue_state,
    fetch_issue_title,
)


def _parse_issues(raw: str) -> list[int]:
    """Parse a comma-separated list of issue numbers."""
    return [int(s.strip()) for s in raw.split(",")]


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments for batch subclause implementation."""
    parser = argparse.ArgumentParser(
        prog="implement_subclauses",
        description="Invoke implement_subclause for multiple issues.",
    )
    add_lrm_arg(parser)
    parser.add_argument(
        "--issues",
        type=_parse_issues,
        required=True,
        help="Comma-separated GitHub issue numbers (e.g. 336,337,338).",
    )
    parser.add_argument(
        "--organization", required=True,
        help="GitHub organization.",
    )
    parser.add_argument(
        "--repo", required=True,
        help="GitHub repository.",
    )
    add_model_arg(parser)
    return parse_and_validate(parser, argv)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> None:
    """Parse args, resolve subclauses from issue titles, and implement."""
    args = parse_args(argv)
    lrm = str(args.lrm)

    subclauses = []
    for issue_num in args.issues:
        title = fetch_issue_title(args.organization, args.repo, issue_num)
        subclause = extract_subclause_from_title(title)
        if not subclause:
            print(f"WARNING: Could not extract subclause from issue"
                  f" #{issue_num} title: {title!r}")
            continue
        state = fetch_issue_state(
            args.organization, args.repo, issue_num,
        )
        if state == "closed":
            print(f"Skipping #{issue_num} (closed).")
            continue
        subclauses.append((subclause, issue_num))

    for i, (subclause, issue_num) in enumerate(subclauses):
        continue_session = i > 0
        children = sorted(
            s for s, _ in subclauses if s.startswith(subclause + ".")
        )
        exclude = ",".join(children)
        invoke_implement_subclause(
            lrm, subclause, issue_num,
            model=args.model,
            continue_session=continue_session,
            exclude=exclude,
        )
