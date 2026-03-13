"""Shared CLI argument helpers for implementation scripts."""

import argparse
import dataclasses
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


def parse_and_validate(
    parser: argparse.ArgumentParser, argv: list[str] | None = None,
) -> argparse.Namespace:
    """Parse *argv* and validate the LRM path."""
    args = parser.parse_args(argv)
    validate_lrm(parser, args)
    return args


# ---------------------------------------------------------------------------
# Dataclasses for subprocess invocation
# ---------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True)
class SubclauseParams:
    """Batch-constant parameters for ``invoke_implement_subclause``."""

    lrm: str
    issue: int
    model: str


@dataclasses.dataclass(frozen=True)
class ClauseParams:
    """Batch-constant parameters for ``invoke_implement_clause``."""

    lrm: str
    master_issue: int
    organization: str
    repo: str


def add_github_args(parser: argparse.ArgumentParser) -> None:
    """Add ``--master-issue``, ``--organization``, and ``--repo`` to *parser*."""
    parser.add_argument(
        "--master-issue",
        type=int,
        required=True,
        help="GitHub master tracking issue number.",
    )
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
        except ValueError as exc:
            raise argparse.ArgumentTypeError(
                f"Invalid issue number '{value}' for clause '{key}'. "
                "Expected an integer.",
            ) from exc
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
    params: SubclauseParams,
    subclause: str,
    continue_session: bool,
    exclude: str = "",
) -> None:
    """Shell out to ``python -m implement_subclause``."""
    print(f"Invoking implement_subclause for {subclause}...")
    cmd = [
        sys.executable, "-m", "implement_subclause",
        "--lrm", params.lrm,
        "--subclause", subclause,
        "--issue", str(params.issue),
        "--model", params.model,
    ]
    if continue_session:
        cmd.append("--continue")
    if exclude:
        cmd.extend(["--exclude", exclude])
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(result.returncode)


def invoke_implement_subclauses(
    params: ClauseParams,
    subclauses: list[str],
    clause_issue: int,
    *,
    model: str = "opus",
) -> None:
    """Shell out to ``python -m implement_subclauses``."""
    print(f"Invoking implement_subclauses for {','.join(subclauses)}...")
    cmd = [
        sys.executable, "-m", "implement_subclauses",
        "--lrm", params.lrm,
        "--subclauses", ",".join(subclauses),
        "--clause-issue", str(clause_issue),
        "--master-issue", str(params.master_issue),
        "--organization", params.organization,
        "--repo", params.repo,
        "--model", model,
    ]
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(result.returncode)


def invoke_implement_clause(
    params: ClauseParams, clause: str, sub_issue: int,
) -> None:
    """Shell out to ``python -m implement_clause``."""
    print(f"Invoking implement_clause for clause {clause} (issue #{sub_issue})...")
    cmd = [
        sys.executable, "-m", "implement_clause",
        "--lrm", params.lrm,
        "--clause", clause,
        "--sub-issue", str(sub_issue),
        "--master-issue", str(params.master_issue),
        "--organization", params.organization,
        "--repo", params.repo,
    ]
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(result.returncode)
