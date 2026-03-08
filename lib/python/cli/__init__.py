"""Shared CLI argument helpers for implementation scripts."""

import argparse
import subprocess
import sys
from pathlib import Path


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
