"""Shared CLI argument helpers for implementation scripts."""

import argparse
import re
import subprocess
import sys
from pathlib import Path

CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


def add_lrm_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--lrm`` argument to *parser*."""
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the LRM PDF.",
    )


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


def parse_clause_issues(raw: str) -> dict[str, int]:
    """Parse comma-separated ``clause=issue`` pairs.

    Returns a dict mapping clause strings to integer issue numbers.
    """
    pairs = [s.strip() for s in raw.split(",")]
    result: dict[str, int] = {}
    for pair in pairs:
        if "=" not in pair:
            raise argparse.ArgumentTypeError(
                f"Invalid clause=issue pair: '{pair}'. Expected format: 15=17",
            )
        key, value = pair.split("=", 1)
        key = key.strip()
        value = value.strip()
        if not CLAUSE_RE.match(key):
            raise argparse.ArgumentTypeError(
                f"Invalid clause format '{key}'. "
                "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
                "(V is a number or uppercase letter; "
                "remaining parts are numbers).",
            )
        try:
            result[key] = int(value)
        except ValueError:
            raise argparse.ArgumentTypeError(
                f"Invalid issue number '{value}' for clause '{key}'. "
                "Expected an integer.",
            )
    return result


def add_clauses_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--clauses`` argument to *parser*."""
    parser.add_argument(
        "--clauses",
        type=parse_clause_issues,
        required=True,
        help="Comma-separated clause=issue pairs (e.g. 15=17,16=18).",
    )


def invoke_implement_subclause(
    lrm: str,
    subclause: str,
    issue: int,
    model: str,
    continue_session: bool,
) -> None:
    """Shell out to ``python -m implement_subclause``."""
    print(f"Invoking implement_subclause for {subclause}...")
    cmd = [
        sys.executable, "-m", "implement_subclause",
        "--lrm", lrm,
        "--subclause", subclause,
        "--issue", str(issue),
        "--model", model,
    ]
    if continue_session:
        cmd.append("--continue")
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(result.returncode)


def invoke_implement_clause(
    lrm: str,
    clause: str,
    sub_issue: int,
    master_issue: int,
    organization: str,
    repo: str,
) -> None:
    """Shell out to ``python -m implement_clause``."""
    print(f"Invoking implement_clause for clause {clause} (issue #{sub_issue})...")
    cmd = [
        sys.executable, "-m", "implement_clause",
        "--lrm", lrm,
        "--clause", clause,
        "--sub-issue", str(sub_issue),
        "--master-issue", str(master_issue),
        "--organization", organization,
        "--repo", repo,
    ]
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(result.returncode)
