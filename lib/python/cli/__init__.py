"""Shared CLI argument helpers for implementation scripts."""

import argparse
import re
from pathlib import Path

# The first alternative matches an identifier with no dot, and that is
# deliberate. Five entries of IEEE 1800-2023 have nothing numbered beneath
# them, so the only way to name one is by its own identifier: clauses 2 and
# 41, and annexes B, P and Q. Requiring a dot here would put those five out
# of reach. Every other value admitted really is a subclause, because §1.5
# calls a numbered division of a clause a subclause and Annex A's opening
# calls a numbered division of an annex the same thing.
SUBCLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")

# What the subclause arguments admit, worded once so the help text and both
# rejection messages say the same thing. The two clauses and three annexes
# are named rather than described, because the standard has no word covering
# a clause, a subclause and an annex together: it enumerates them, as Annex
# A does with "the clauses and annexes of this standard".
_SUBCLAUSE_FORMS = (
    "V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z"
    " (V is a number or uppercase letter; remaining parts are numbers),"
    " or one of the entries with no subclauses of their own:"
    " 2, 41, B, P, Q"
)


def add_lrm_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--lrm`` argument to *parser*."""
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the LRM PDF.",
    )


def add_subclause_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--subclause`` argument to *parser*."""
    parser.add_argument(
        "--subclause",
        type=str,
        required=True,
        help=f"LRM subclause number: {_SUBCLAUSE_FORMS}.",
    )


def validate_subclause(
    parser: argparse.ArgumentParser, args: argparse.Namespace,
) -> None:
    """Error out unless ``args.subclause`` names a subclause, or one of the
    clauses and annexes that have no subclauses of their own.
    """
    if not SUBCLAUSE_RE.match(args.subclause):
        parser.error(
            f"Invalid subclause format '{args.subclause}'. "
            f"Expected {_SUBCLAUSE_FORMS}."
        )


def parse_and_validate_subclause(
    parser: argparse.ArgumentParser,
    argv: list[str] | None = None,
) -> argparse.Namespace:
    """Parse *argv* and validate both ``--lrm`` and ``--subclause``."""
    args = parser.parse_args(argv)
    validate_lrm(parser, args)
    validate_subclause(parser, args)
    return args


def add_model_arg(
    parser: argparse.ArgumentParser, *, default: str = "opus",
) -> None:
    """Add the ``--model`` argument to *parser*.

    *default* lets a caller override the built-in ``opus`` default when
    a script's per-call workload favours a different model — the
    dependency-graph generator runs Sonnet because each oracle call is
    a focused read-and-list judgment, not a long agentic loop.
    """
    parser.add_argument(
        "--model",
        type=str,
        default=default,
        help=f"Claude model to use (default: {default}).",
    )


def add_effort_arg(
    parser: argparse.ArgumentParser, *, default: str = "medium",
) -> None:
    """Add the ``--effort`` argument to *parser*.

    Maps to the Claude CLI's ``--effort`` flag, which sets the
    thinking-budget tier for the session. Constrained to the CLI's
    accepted values so a typo errors at parse time rather than failing
    deep inside the subprocess call.
    """
    parser.add_argument(
        "--effort",
        type=str,
        default=default,
        choices=["low", "medium", "high", "xhigh", "max"],
        help=f"Claude CLI thinking-effort level (default: {default}).",
    )


def validate_lrm(parser: argparse.ArgumentParser, args: argparse.Namespace) -> None:
    """Error out if the LRM file does not exist."""
    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")


def parse_and_validate(
    parser: argparse.ArgumentParser, argv: list[str] | None = None,
) -> argparse.Namespace:
    """Parse *argv* and validate the LRM path."""
    args = parser.parse_args(argv)
    validate_lrm(parser, args)
    return args


def parse_labels(raw: str) -> list[str]:
    """Split a comma-separated label string into a list."""
    return [s.strip() for s in raw.split(",")]


def parse_subclauses(raw: str) -> list[str]:
    """Split a comma-separated list and validate each entry, which names a
    subclause or one of the clauses and annexes that have none.
    """
    parts = [s.strip() for s in raw.split(",")]
    for part in parts:
        if not SUBCLAUSE_RE.match(part):
            raise argparse.ArgumentTypeError(
                f"Invalid subclause format '{part}'. "
                f"Expected {_SUBCLAUSE_FORMS}."
            )
    return parts


def add_labels_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--labels`` argument to *parser*."""
    parser.add_argument(
        "--labels",
        type=parse_labels,
        required=True,
        help="Comma-separated GitHub labels (e.g. 'IEEE 1800-2023,bug').",
    )
