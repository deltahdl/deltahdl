"""Names the subclause a campaign should take next, and its issue.

``next_subclause`` prints one line — the subclause and the number of the
issue tracking it — so that whatever is choosing what to work on reads
one answer instead of the whole open backlog. It changes nothing: the
graph, the issues and the repository are all read and none is written.
"""

import argparse
import sys
from pathlib import Path

from lib.python.github import format_subclause_label, list_open_issues

from .pipeline import load_order, next_subclause


# The graph the dependency generator writes, at its committed location.
GRAPH_PATH = (
    Path(__file__).resolve().parents[2] / "docs" / "dependency_graph.json"
)

_DESCRIPTION = (
    "Name the earliest subclause in the recorded dependency order that"
    " still has an open issue tracking it, and that issue's number."
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    parser.add_argument(
        "--graph",
        type=Path,
        default=GRAPH_PATH,
        help="Path to the recorded dependency graph.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    """Print the next subclause and its issue, or report there is none.

    Exits non-zero when the order holds no subclause with an open issue.
    That is the campaign having finished rather than a fault, but it is
    still not an answer to the question that was asked, and a caller
    substituting the empty line for one would act on nothing.
    """
    args = parse_args(argv)
    found = next_subclause(load_order(args.graph), list_open_issues())
    if found is None:
        print(
            "No subclause in the dependency order has an open issue"
            " tracking it.",
            file=sys.stderr,
        )
        sys.exit(1)
    subclause, number = found
    print(f"{format_subclause_label(subclause)} #{number}")
