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

_JOBS_DEFAULT = 16


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
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
    if not output.exists():
        return {}
    records: dict[str, Any] = json.loads(output.read_text()).get(
        "records", {},
    )
    return records


def _write_checkpoint(
    output: Path, records: dict[str, Any], walked: list[str],
) -> None:
    ordered = {sub: records[sub] for sub in walked if sub in records}
    order = order_groups(find_cycle_groups(ordered), ordered)
    payload = json.dumps({"records": ordered, "order": order}, indent=2)
    partial = output.with_name(output.name + ".partial")
    partial.write_text(payload)
    partial.replace(output)


def _checkpoint_message(recorded: int, total: int) -> str:
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
        _write_checkpoint(args.output, records, walked)
        if args.commit:
            commit_output(
                args.output,
                message=_checkpoint_message(len(records), len(walked)),
            )

    _walk_records(walked, records, args, _checkpoint)
