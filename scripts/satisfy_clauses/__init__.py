"""User-facing entry point for batch clause satisfaction.

``satisfy_clauses --clauses X[,Y]…`` invokes ``satisfy_clause`` for
each entry in input order. With this script the four-script chain
``satisfy_clauses -> satisfy_clause -> satisfy_subclauses ->
satisfy_subclause`` is complete: each layer delegates to the
next-most-specific tool exactly once.
"""

import argparse

from lib.python.cli import (
    add_clauses_arg,
    add_labels_arg,
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
)

from .pipeline import satisfy_clauses


_DESCRIPTION = (
    "Idempotently satisfy a list of LRM clauses by invoking"
    " satisfy_clause for each entry in input order."
)


def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_clauses_arg(parser)
    add_model_arg(parser)
    add_labels_arg(parser)
    return parse_and_validate(parser, argv)


def main(argv=None) -> None:
    """Run satisfy_clause for each requested clause."""
    args = parse_args(argv)
    satisfy_clauses(
        args.clauses, str(args.lrm),
        model=args.model, labels=args.labels,
    )
