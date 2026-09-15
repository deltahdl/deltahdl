import argparse
import sys
from pathlib import Path

from lib.python.github import format_subclause_label, list_open_issues

from .pipeline import load_order, next_subclause


GRAPH_PATH = (
    Path(__file__).resolve().parents[2] / "docs" / "dependency_graph.json"
)

_DESCRIPTION = (
    "Name the earliest subclause in the recorded dependency order that"
    " still has an open issue tracking it, and that issue's number."
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    parser.add_argument(
        "--graph",
        type=Path,
        default=GRAPH_PATH,
        help="Path to the recorded dependency graph.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
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
