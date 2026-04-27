"""User-facing entry point for batch subclause satisfaction.

``satisfy_subclauses --subclauses X.Y[,X.Y[.Z]]…`` invokes
``satisfy_subclause`` for each entry in input order. Idempotence comes
for free from ``satisfy_subclause`` itself; this wrapper adds nothing
beyond list parsing and ordering.
"""

import argparse

from lib.python.cli import (
    add_labels_arg,
    add_lrm_arg,
    add_model_arg,
    add_subclauses_arg,
    parse_and_validate,
)

from .pipeline import satisfy_subclauses


_DESCRIPTION = (
    "Idempotently satisfy a list of LRM subclauses by invoking"
    " satisfy_subclause for each entry in input order."
)


def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_subclauses_arg(parser)
    add_model_arg(parser)
    add_labels_arg(parser)
    return parse_and_validate(parser, argv)


def main(argv=None) -> None:
    """Run satisfy_subclause for each requested subclause."""
    args = parse_args(argv)
    satisfy_subclauses(
        args.subclauses, str(args.lrm),
        model=args.model, labels=args.labels,
    )
