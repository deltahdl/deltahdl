"""Batch wrapper around implement_clause for multiple clauses.

Loops through clause=issue pairs, invoking implement_clause for each one.
"""

import argparse

from lib.python.cli import (
    add_clauses_arg,
    add_github_args,
    add_lrm_arg,
    invoke_implement_clause,
    validate_lrm,
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments for batch clause implementation."""
    parser = argparse.ArgumentParser(
        prog="implement_clauses",
        description="Invoke implement_clause for multiple clauses.",
    )
    add_lrm_arg(parser)
    add_clauses_arg(parser)
    add_github_args(parser)
    args = parser.parse_args(argv)

    validate_lrm(parser, args)

    return args


def main(argv: list[str] | None = None) -> None:
    """Parse args and invoke implement_clause for each clause."""
    args = parse_args(argv)
    lrm = str(args.lrm)

    for clause, sub_issue in args.clauses.items():
        invoke_implement_clause(
            lrm, clause, sub_issue,
            args.master_issue, args.organization, args.repo,
        )
