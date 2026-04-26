"""User-facing entry point for the satisfaction pipeline.

``satisfy_subclause --subclause X --lrm path`` finds-or-creates a
GitHub issue for §X, recursively satisfies its dependencies, then
runs the eight-step audit-then-act mutator once. Convergence emerges
from the working tree: any edits the mutator produced are committed
with a ``Closes #N`` trailer; an empty diff means §X is already
satisfied.
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
    "Idempotently satisfy an LRM subclause. Finds-or-creates an issue,"
    " recursively satisfies dependencies, and runs the eight-step"
    " audit-then-act mutator. The mutator's commit step is the"
    " convergence signal."
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
