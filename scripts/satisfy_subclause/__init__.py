"""User-facing entry point for the satisfaction pipeline.

``satisfy_subclause --subclause X --lrm path`` is idempotent: if §X is
already satisfied (per the satisfaction oracle), it does nothing.
Otherwise it runs the recursive pipeline defined in :mod:`pipeline`,
labels the issue ``pipeline-stuck`` if the retry budget is exhausted,
and exits non-zero on failure.
"""

import argparse

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    parse_and_validate_subclause,
)

from .pipeline import satisfy_subclause


_DESCRIPTION = (
    "Idempotently satisfy an LRM subclause. Runs the satisfaction"
    " oracle, recursively satisfies dependencies, dispatches the"
    " appropriate mutator, and labels the issue pipeline-stuck if"
    " the retry budget is exhausted."
)


def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    add_model_arg(parser)
    return parse_and_validate_subclause(parser, argv)


def main(argv=None) -> None:
    """Run the satisfaction pipeline for the requested subclause."""
    args = parse_args(argv)
    satisfy_subclause(args.subclause, str(args.lrm), model=args.model)
