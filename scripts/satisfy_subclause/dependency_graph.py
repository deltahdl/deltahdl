"""Recorded dependency answers, read in place of a fresh oracle call.

``generate_lrm_subclause_dependencies`` walks the LRM once, asks the
dependency oracle about every subclause, and writes the answers to a
JSON file. This module reads that file back, so the recursion can look
an answer up instead of buying the same answer again on every frame it
enters. Asking once and reading many times is the cheaper arrangement,
and it is also the repeatable one: the oracle is free to word its
answer differently on a second asking, while a file says the same
thing every time it is read.

A recorded answer is trusted only where it still passes the checks a
fresh answer has to pass. The file was written before later changes to
what an answer is allowed to contain, so each recorded list goes
through ``validate_dependencies`` first.

The oracle is never taken out of reach. Nothing that can happen to the
file — being absent, being unreadable, not mentioning a subclause, or
holding an answer the checks reject — does more than send that
question to the oracle, which is where every question went before the
file existed. The file makes the campaign cheaper and repeatable; it
is never the only way to get an answer.
"""

import json
import sys
from functools import cache
from pathlib import Path
from typing import Any

from lib.python.lrm import load_toc
from lib.python.lrm_subclause_dependencies import (
    SubclauseDependencies,
    compute_subclause_dependencies,
    validate_dependencies,
)


# The graph the generator writes, at its committed location. Named here
# rather than passed down the recursion because every frame of a pass
# reads the same file.
GRAPH_PATH = (
    Path(__file__).resolve().parents[2] / "docs" / "dependency_graph.json"
)


@cache
def load_dependency_graph(path: Path) -> dict[str, SubclauseDependencies]:
    """Return the recorded dependency list for each subclause in ``path``.

    No state of the file is allowed to stop a campaign. An absent file
    means no walk has been recorded yet. A file that cannot be read as
    a graph — truncated, hand-edited into invalid JSON, or missing the
    records the generator writes — means the recording is unusable.
    Both read as no recorded answers at all, which sends every
    subclause to the oracle, exactly as the campaign behaved before any
    graph existed. The oracle is the answer of last resort and stays
    reachable whatever has happened to the file.

    Both are announced on stderr, and the unreadable case is announced
    as a fault. A campaign paying for an answer per frame should say so
    rather than look identical to one reading them off disk, and a
    broken graph should say what is wrong with it rather than show up
    only as a larger bill.

    Memoized by path, so one pass reads the file once however many
    frames it enters.
    """
    if not path.exists():
        print(
            f"Dependency graph {path} is absent;"
            " every subclause's dependencies will be asked of the oracle.",
            file=sys.stderr,
        )
        return {}
    try:
        payload: dict[str, Any] = json.loads(path.read_text())
        records: dict[str, dict[str, Any]] = payload["records"]
        return {
            subclause: list(record["dependencies"])
            for subclause, record in records.items()
        }
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
        print(
            f"WARNING: dependency graph {path} cannot be read ({exc});"
            " every subclause's dependencies will be asked of the oracle."
            " Rebuild the graph to stop paying for them.",
            file=sys.stderr,
        )
        return {}


def resolve_dependencies(
    subclause: str, lrm: str, *, model: str, effort: str,
) -> SubclauseDependencies:
    """Return the dependencies of ``subclause``, recorded ones preferred.

    Reads the recorded answer when the graph holds one and it still
    passes today's checks, and asks the oracle otherwise. A rejected
    recording is reported on stderr and then treated as a miss, so the
    campaign proceeds on a fresh answer rather than on a stale one.
    """
    recorded = load_dependency_graph(GRAPH_PATH).get(subclause)
    if recorded is not None:
        try:
            return validate_dependencies(recorded, toc=load_toc(lrm))
        except ValueError as exc:
            print(
                f"WARNING: recorded dependencies for §{subclause} are no"
                f" longer acceptable ({exc}); asking the oracle instead.",
                file=sys.stderr,
            )
    return compute_subclause_dependencies(
        subclause, lrm, model=model, effort=effort,
    )
