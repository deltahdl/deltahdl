"""Batch wrapper around implement_subclause for multiple subclauses.

Loops through a comma-separated list of subclauses, invoking
implement_subclause for each one, then optionally closes the clause
issue and marks it done on the master issue.
"""

import argparse
import re

from lib.python.cli import (
    add_continue_arg,
    add_lrm_arg,
    add_model_arg,
    invoke_implement_subclause,
    validate_lrm,
)
from lib.python.github import (
    close_issue,
    fetch_issue_body,
    mark_master_complete,
    next_unchecked,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


# ---------------------------------------------------------------------------
# Subclause parsing
# ---------------------------------------------------------------------------

def parse_subclauses(raw: str) -> list[str]:
    """Split and validate a comma-separated list of subclauses."""
    parts = [s.strip() for s in raw.split(",")]
    for part in parts:
        if not CLAUSE_RE.match(part):
            raise argparse.ArgumentTypeError(
                f"Invalid subclause format '{part}'. "
                "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
                "(V is a number or uppercase letter; "
                "remaining parts are numbers)."
            )
    return parts


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments for batch subclause implementation."""
    parser = argparse.ArgumentParser(
        prog="implement_subclauses",
        description="Invoke implement_subclause for multiple subclauses.",
    )
    add_lrm_arg(parser)
    parser.add_argument(
        "--subclauses",
        type=parse_subclauses,
        required=True,
        help="Comma-separated LRM subclause numbers (e.g. 6.6.4.1,6.6.4.2).",
    )
    parser.add_argument(
        "--clause-issue",
        type=int,
        required=True,
        help="GitHub issue number for the clause.",
    )
    parser.add_argument(
        "--master-issue",
        type=int,
        required=True,
        help="GitHub master tracking issue number.",
    )
    parser.add_argument(
        "--organization",
        required=True,
        help="GitHub organization.",
    )
    parser.add_argument(
        "--repo",
        required=True,
        help="GitHub repository.",
    )
    add_model_arg(parser)
    add_continue_arg(parser)
    args = parser.parse_args(argv)

    validate_lrm(parser, args)

    return args


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> None:
    """Parse args, loop subclauses, and optionally close the clause issue."""
    args = parse_args(argv)
    lrm = str(args.lrm)
    subclauses = args.subclauses

    for i, subclause in enumerate(subclauses):
        continue_session = args.continue_session if i == 0 else True
        invoke_implement_subclause(
            lrm, subclause, args.clause_issue,
            args.model, continue_session,
        )

    body = fetch_issue_body(
        args.organization, args.repo, args.clause_issue,
    )
    if next_unchecked(body) is None:
        close_issue(
            args.organization, args.repo, args.clause_issue,
            "all subclauses are implemented",
        )
        mark_master_complete(
            args.organization, args.repo,
            args.master_issue, args.clause_issue,
        )
