"""Generate the LRM dependency graph as a JSON file.

``document_dependency_graph --lrm path --output graph.json`` walks the
LRM table of contents, asks the read-only oracles once per subclause,
and writes the resulting graph to disk so downstream tools can plan a
satisfaction pass without re-querying Claude on every recursion.
"""

import argparse
import json
from pathlib import Path

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
)
from lib.python.lrm import load_toc

from .ordering import find_cycle_groups, order_groups
from .walk import build_subclause_record


_DESCRIPTION = (
    "Walk the LRM, ask the dependency oracles once per subclause, and"
    " write the resulting graph to a JSON file so downstream tools"
    " can plan a satisfaction pass without re-querying."
)


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
    """Run the dependency oracles for every subclause and write the graph."""
    args = parse_args(argv)
    toc = load_toc(str(args.lrm))
    records = {
        subclause: build_subclause_record(
            subclause, str(args.lrm), model=args.model,
        )
        for subclause in toc
    }
    order = order_groups(find_cycle_groups(records), records)
    args.output.write_text(json.dumps({"records": records, "order": order}))
