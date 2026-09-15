"""Shared CLI argument helpers for implementation scripts."""

import argparse
from pathlib import Path


def add_lrm_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--lrm`` argument to *parser*."""
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the LRM PDF.",
    )


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


