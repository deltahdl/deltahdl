"""User-facing entry point for batch subclause satisfaction.

Two modes (mutually exclusive):

* ``satisfy_subclauses --subclauses X.Y[,X.Y[.Z]]…`` invokes
  ``satisfy_subclause`` for each entry in input order.
* ``satisfy_subclauses --issue N`` walks the master tracking issue
  #N (e.g. #1 for IEEE 1800-2023), find-or-creates a sub-issue for
  each unlinked ``§X.Y`` entry, patches the master body, then runs
  ``satisfy_subclause``. Linked ``#NNN`` entries dispatch (open) or
  loud-skip (closed).
"""

import argparse

from lib.python.cli import (
    add_labels_arg,
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
    parse_subclauses,
)

from .pipeline import satisfy_subclauses, satisfy_subclauses_from_issue


_DESCRIPTION = (
    "Idempotently satisfy LRM subclauses by invoking satisfy_subclause"
    " for each entry. Either pass --subclauses with a comma-separated"
    " list, or --issue N to drive from the master tracking issue's body."
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    add_lrm_arg(parser)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "--subclauses",
        type=parse_subclauses,
        default=None,
        help="Comma-separated subclauses (e.g. '33.1,33.4,A.5,B').",
    )
    group.add_argument(
        "--issue",
        type=int,
        default=None,
        help="Master tracking issue number whose body lists the work.",
    )
    add_model_arg(parser)
    add_labels_arg(parser)
    return parse_and_validate(parser, argv)


def main(argv: list[str] | None = None) -> None:
    """Dispatch to the subclauses-list or issue-driven entry point."""
    args = parse_args(argv)
    if args.issue is not None:
        satisfy_subclauses_from_issue(
            args.issue, str(args.lrm),
            model=args.model, labels=args.labels,
        )
        return
    satisfy_subclauses(
        args.subclauses, str(args.lrm),
        model=args.model, labels=args.labels,
    )
