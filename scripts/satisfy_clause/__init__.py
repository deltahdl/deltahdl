"""User-facing entry point for clause satisfaction.

``satisfy_clause --clause X`` enumerates every descendant subclause
of §X from the LRM TOC and hands the list to ``satisfy_subclauses``,
which loops over ``satisfy_subclause`` per entry. The chain is
``satisfy_clause -> satisfy_subclauses -> satisfy_subclause``; this
script does not loop over ``satisfy_subclause`` directly because that
would duplicate the iteration logic that already lives in
``satisfy_subclauses``.
"""

import argparse

from lib.python.cli import (
    add_clause_arg,
    add_labels_arg,
    add_lrm_arg,
    add_model_arg,
    parse_and_validate_clause,
)

from .pipeline import satisfy_clause


_DESCRIPTION = (
    "Idempotently satisfy an LRM clause by enumerating every"
    " descendant subclause from the TOC and invoking"
    " satisfy_subclauses for the list."
)


def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_clause_arg(parser)
    add_model_arg(parser)
    add_labels_arg(parser)
    return parse_and_validate_clause(parser, argv)


def main(argv=None) -> None:
    """Run satisfy_subclauses across §clause's descendants."""
    args = parse_args(argv)
    satisfy_clause(
        args.clause, str(args.lrm),
        model=args.model, labels=args.labels,
    )
