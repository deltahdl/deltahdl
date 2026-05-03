"""Generate the LRM dependency graph as a JSON file.

``document_dependency_graph --lrm path --output graph.json`` calls the
read-only dependency oracle and writes the resulting graph to disk so
downstream tools can plan a satisfaction pass without re-querying
Claude on every recursion.
"""

import argparse
import json
from pathlib import Path

from satisfy_subclause.oracles import compute_subclause_dependencies

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
)


_DESCRIPTION = (
    "Walk the LRM, ask the dependency oracle once per subclause, and"
    " write the resulting graph to a JSON file so downstream tools"
    " can plan a satisfaction pass without re-querying."
)

_PLACEHOLDER_SUBCLAUSE = "4.4"


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_model_arg(parser)
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="Path the dependency graph JSON file is written to.",
    )
    return parse_and_validate(parser, argv)


def main(argv: list[str] | None = None) -> None:
    """Run the dependency oracle and write the graph file."""
    args = parse_args(argv)
    deps = compute_subclause_dependencies(
        _PLACEHOLDER_SUBCLAUSE, str(args.lrm), model=args.model,
    )
    args.output.write_text(json.dumps({_PLACEHOLDER_SUBCLAUSE: deps}))
