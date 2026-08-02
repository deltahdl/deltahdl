"""Generate the LRM dependency graph as a JSON file.

``generate_lrm_subclause_dependencies --lrm path --output graph.json`` walks the
LRM table of contents, asks the read-only oracles once per subclause,
and writes the resulting graph to disk so downstream tools can plan a
satisfaction pass without re-querying Claude on every recursion.
"""

import argparse
import json
from collections.abc import Callable
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any

from lib.python.cli import (
    add_effort_arg,
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
)
from lib.python.lrm import is_top_level_aggregate, load_toc

from .commit import assert_clean_tree, commit_output
from .ordering import find_cycle_groups, order_groups
from .walk import build_subclause_record


_DESCRIPTION = (
    "Walk the LRM, ask the dependency oracles once per subclause, and"
    " write the resulting graph to a JSON file so downstream tools"
    " can plan a satisfaction pass without re-querying."
)

# How many oracle calls a walk runs at once when --jobs is not given.
# One call takes around 37 seconds, nearly all of it a session reading
# the LRM rather than the walk doing anything, and the table of
# contents holds about 1,700 walkable subclauses. One call at a time is
# therefore something like seventeen hours, and sixteen at a time is
# something like one.
_JOBS_DEFAULT = 16


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(prog=__package__, description=_DESCRIPTION)
    add_lrm_arg(parser)
    add_model_arg(parser, default="sonnet")
    add_effort_arg(parser)
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="Path the dependency graph JSON file is written to.",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=_JOBS_DEFAULT,
        help=(
            "How many oracle calls run at once. A call spends nearly"
            " all of its time waiting on a session that is reading the"
            " LRM, so the walk takes roughly one call's time multiplied"
            " by the number of subclauses and divided by this number."
            " Pass 1 to run the calls one after another."
        ),
    )
    parser.add_argument(
        "--commit",
        action="store_true",
        default=False,
        help=(
            "After writing each checkpoint, stage, commit, and push it"
            " to main so progress is durable across crashes. Off by"
            " default."
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
            " checkpoint write."
        ),
    )
    args = parse_and_validate(parser, argv)
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    return args


def _load_checkpoint(output: Path) -> dict[str, Any]:
    """Return the cached records dict from ``output``, or empty if absent.

    A pre-existing --output file lets a resumed run skip oracle calls
    for subclauses that already have a record. Malformed JSON raises
    so a corrupt checkpoint becomes a loud failure rather than a silent
    rerun-from-scratch.
    """
    if not output.exists():
        return {}
    records: dict[str, Any] = json.loads(output.read_text()).get(
        "records", {},
    )
    return records


def _write_checkpoint(
    output: Path, records: dict[str, Any], walked: list[str],
) -> None:
    """Write the records for *walked* and their dependency order to *output*.

    The records are written in *walked* order rather than the order
    they were answered in. Answers arrive in whatever order the oracle
    calls happen to finish, which differs from one run to the next, and
    a graph file whose entries reshuffled on every rebuild would show a
    whole-file diff for a handful of changed answers.

    The payload goes to a file beside *output* and is then moved into
    place, so a reader sees either the previous checkpoint or this one
    and never a partly written file. That matters because this file is
    what a resumed run reads to find out which answers have already
    been paid for: a half-written one is a file the resumed run raises
    on, and the whole walk has to be bought again.
    """
    ordered = {sub: records[sub] for sub in walked if sub in records}
    order = order_groups(find_cycle_groups(ordered), ordered)
    payload = json.dumps({"records": ordered, "order": order}, indent=2)
    partial = output.with_name(output.name + ".partial")
    partial.write_text(payload)
    partial.replace(output)


def _checkpoint_message(recorded: int, total: int) -> str:
    """Return the checkpoint commit message for *recorded* of *total* answers.

    A checkpoint covers however many subclauses were answered since the
    last one, so the message counts answers rather than naming one of
    them.
    """
    return (
        f"generate_lrm_subclause_dependencies: "
        f"checkpoint {recorded}/{total} answered"
    )


def _walk_records(
    walked: list[str],
    records: dict[str, Any],
    args: argparse.Namespace,
    checkpoint: Callable[[], None],
) -> None:
    """Fill *records* with an answer for every entry of *walked* it lacks.

    The oracle calls run ``--jobs`` at a time. Each one is built from
    its subclause identifier alone and is read by nothing until every
    answer exists, so overlapping them yields the records a
    one-at-a-time walk yields, and the walk finishes when the slowest
    call does rather than when the sum of them does.

    *checkpoint* is called once every ``--jobs`` answers, and again on
    the way out whenever answers are in hand that no checkpoint has
    written yet — on the failing path as well as the succeeding one.
    Persisting those is what keeps a failure from re-purchasing work
    already paid for, and it is also what writes the file at all when
    every answer came from the cache and no call ran. Queued calls are
    cancelled on the failing path, so a failure costs the calls already
    running and no more instead of working through the rest of the
    table of contents for a walk that cannot finish.
    """
    executor = ThreadPoolExecutor(max_workers=args.jobs)
    written = len(records)
    checkpointed = False
    try:
        pending = {
            executor.submit(
                build_subclause_record, subclause, str(args.lrm),
                model=args.model, effort=args.effort,
            ): subclause
            for subclause in walked if subclause not in records
        }
        for future in as_completed(pending):
            records[pending[future]] = future.result()
            if len(records) - written >= args.jobs:
                written = len(records)
                checkpointed = True
                checkpoint()
    finally:
        executor.shutdown(wait=True, cancel_futures=True)
        if not checkpointed or len(records) != written:
            checkpoint()


def main(argv: list[str] | None = None) -> None:
    """Run the dependency oracles for every subclause and write the graph."""
    args = parse_args(argv)
    toc = load_toc(str(args.lrm))
    cached = _load_checkpoint(args.output) if args.resume else {}
    if args.commit:
        assert_clean_tree()
    walked = [sub for sub in toc if not is_top_level_aggregate(sub, toc)]
    records: dict[str, Any] = {
        sub: cached[sub] for sub in walked if sub in cached
    }

    def _checkpoint() -> None:
        """Persist the answers in hand, committing them when asked to."""
        _write_checkpoint(args.output, records, walked)
        if args.commit:
            commit_output(
                args.output,
                message=_checkpoint_message(len(records), len(walked)),
            )

    _walk_records(walked, records, args, _checkpoint)
