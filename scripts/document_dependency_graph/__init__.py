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

from .commit import commit_output
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
    parser.add_argument(
        "--commit",
        action="store_true",
        default=False,
        help=(
            "After writing the output file, stage, commit, and push it"
            " to main. Off by default."
        ),
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        default=False,
        help=(
            "Read --output as a checkpoint and skip subclauses already"
            " recorded there. Off by default — a fresh run ignores any"
            " pre-existing --output and overwrites it on the first"
            " per-subclause checkpoint write."
        ),
    )
    return parse_and_validate(parser, argv)


def _load_checkpoint(output: Path) -> dict:
    """Return the cached records dict from ``output``, or empty if absent.

    A pre-existing --output file lets a resumed run skip oracle calls
    for subclauses that already have a record. Malformed JSON raises
    so a corrupt checkpoint becomes a loud failure rather than a silent
    rerun-from-scratch.
    """
    if not output.exists():
        return {}
    return json.loads(output.read_text()).get("records", {})


def main(argv: list[str] | None = None) -> None:
    """Run the dependency oracles for every subclause and write the graph."""
    args = parse_args(argv)
    toc = load_toc(str(args.lrm))
    cached = _load_checkpoint(args.output) if args.resume else {}
    records: dict = {}
    for subclause in toc:
        if subclause in cached:
            records[subclause] = cached[subclause]
            continue
        records[subclause] = build_subclause_record(
            subclause, str(args.lrm), model=args.model,
        )
        args.output.write_text(json.dumps({"records": records}))
    order = order_groups(find_cycle_groups(records), records)
    args.output.write_text(json.dumps({"records": records, "order": order}))
    if args.commit:
        commit_output(args.output)
