"""Shared CLI argument helpers for implementation scripts."""

import argparse
import re
import subprocess
import threading
from pathlib import Path
from typing import Any, Callable, TypeVar

_T = TypeVar("_T")

SUBCLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){1,4}$")
CLAUSE_ONLY_RE = re.compile(r"^(\d+|[A-Z])$")


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


def add_clause_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--clause`` argument to *parser*."""
    parser.add_argument(
        "--clause",
        type=str,
        required=True,
        help="LRM clause number (V) — a number or single annex letter.",
    )


def validate_clause(
    parser: argparse.ArgumentParser, args: argparse.Namespace,
) -> None:
    """Error out if ``args.clause`` is not a valid top-level clause string."""
    if CLAUSE_ONLY_RE.match(args.clause):
        return
    if SUBCLAUSE_RE.match(args.clause):
        parser.error(
            f"--clause '{args.clause}' is a subclause; "
            "use satisfy_subclause --subclause instead."
        )
    parser.error(
        f"Invalid clause format '{args.clause}'. "
        "Expected a single number (e.g. 33) or "
        "uppercase annex letter (e.g. A)."
    )


def parse_and_validate_clause(
    parser: argparse.ArgumentParser,
    argv: list[str] | None = None,
) -> argparse.Namespace:
    """Parse *argv* and validate both ``--lrm`` and ``--clause``."""
    args = parser.parse_args(argv)
    validate_lrm(parser, args)
    validate_clause(parser, args)
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


def parse_subclauses(raw: str) -> list[str]:
    """Split a comma-separated subclause list and validate each entry."""
    parts = [s.strip() for s in raw.split(",")]
    for part in parts:
        if not SUBCLAUSE_RE.match(part):
            raise argparse.ArgumentTypeError(
                f"Invalid subclause format '{part}'. "
                "Expected V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z."
            )
    return parts


def parse_clauses(raw: str) -> list[str]:
    """Split a comma-separated clause list and validate each entry."""
    parts = [s.strip() for s in raw.split(",")]
    for part in parts:
        if CLAUSE_ONLY_RE.match(part):
            continue
        if SUBCLAUSE_RE.match(part):
            raise argparse.ArgumentTypeError(
                f"--clauses entry '{part}' is a subclause; "
                "use satisfy_subclauses --subclauses instead."
            )
        raise argparse.ArgumentTypeError(
            f"Invalid clause format '{part}'. "
            "Expected a single number (e.g. 33) or "
            "uppercase annex letter (e.g. A)."
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


def add_subclauses_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--subclauses`` argument to *parser*."""
    parser.add_argument(
        "--subclauses",
        type=parse_subclauses,
        required=True,
        help="Comma-separated subclauses (e.g. '33.1,33.4,A.5').",
    )


def add_clauses_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--clauses`` argument to *parser*."""
    parser.add_argument(
        "--clauses",
        type=parse_clauses,
        required=True,
        help="Comma-separated clauses (e.g. '32,33,A').",
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


def run_with_dots(
    func: Callable[..., _T], *args: Any, **kwargs: Any,
) -> _T:
    """Run *func* while printing dots every few seconds.

    Returns whatever *func* returns.
    """
    stop = threading.Event()

    def _print_dots() -> None:
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


def run_claude_cli(
    cmd: list[str],
    prompt: str,
    *,
    env: dict[str, str],
    timeout: float | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run the Claude CLI and return the completed process.

    Centralises the ``subprocess.run`` call so that callers do not
    duplicate the same keyword arguments.
    """
    kwargs: dict[str, Any] = {
        "input": prompt,
        "capture_output": True,
        "text": True,
        "env": env,
    }
    if timeout is not None:
        kwargs["timeout"] = timeout
    return subprocess.run(cmd, check=False, **kwargs)
