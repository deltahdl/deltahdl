"""Shared CLI argument helpers for implementation scripts."""

import argparse
import re
import subprocess
import threading
from pathlib import Path

SUBCLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){1,4}$")


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
        help="LRM subclause number (V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z).",
    )


def validate_subclause(
    parser: argparse.ArgumentParser, args: argparse.Namespace,
) -> None:
    """Error out if ``args.subclause`` is not a valid subclause string."""
    if not SUBCLAUSE_RE.match(args.subclause):
        parser.error(
            f"Invalid subclause format '{args.subclause}'. "
            "Expected V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "(V is a number or uppercase letter; "
            "remaining parts are numbers). "
            "For a top-level clause, use satisfy_clause --clause instead."
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


def add_model_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--model`` argument to *parser*."""
    parser.add_argument(
        "--model",
        type=str,
        default="opus",
        help="Claude model to use (default: opus).",
    )


def add_continue_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--continue`` argument to *parser*."""
    parser.add_argument(
        "--continue",
        action="store_true",
        default=False,
        dest="continue_session",
        help="Continue the previous Claude conversation.",
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


def add_labels_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--labels`` argument to *parser*."""
    parser.add_argument(
        "--labels",
        type=parse_labels,
        required=True,
        help="Comma-separated GitHub labels (e.g. 'IEEE 1800-2023,bug').",
    )


def add_github_args(parser: argparse.ArgumentParser) -> None:
    """Add ``--organization`` and ``--repo`` to *parser*."""
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


_DOT_INTERVAL_SECONDS = 5


def run_with_dots(func, *args, **kwargs):
    """Run *func* while printing dots every few seconds.

    Returns whatever *func* returns.
    """
    stop = threading.Event()

    def _print_dots():
        while not stop.wait(_DOT_INTERVAL_SECONDS):
            print(".", end="", flush=True)

    dot_thread = threading.Thread(target=_print_dots, daemon=True)
    dot_thread.start()
    try:
        return func(*args, **kwargs)
    finally:
        stop.set()
        dot_thread.join()
        print()


def run_claude_cli(cmd, prompt, *, env, timeout=None):
    """Run the Claude CLI and return the completed process.

    Centralises the ``subprocess.run`` call so that callers do not
    duplicate the same keyword arguments.
    """
    kwargs = {
        "input": prompt,
        "capture_output": True,
        "text": True,
        "env": env,
    }
    if timeout is not None:
        kwargs["timeout"] = timeout
    return subprocess.run(cmd, check=False, **kwargs)
