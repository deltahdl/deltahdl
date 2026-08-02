"""Which subclause comes next, and which issue is tracking it.

A campaign that reads every open issue before choosing one pays for the
whole backlog on every choice, and the bill grows with each issue the
work itself files. The dependency graph already holds an order that
answers the question without reading anything: a subclause whose
dependencies are unmet cannot be taken first whatever its issue says, so
the earliest entry in that order still tracked by an open issue is the
one to take. Reading is then one listing rather than one listing per
candidate, and the answer does not change with how many issues exist.
"""

import json
from pathlib import Path
from typing import Any

from lib.python.github import issue_title_for


def load_order(path: Path) -> list[list[str]]:
    """Return the dependency order recorded in the graph at *path*.

    The order is a list of groups. Every dependency of a subclause in a
    group is satisfied by some earlier group, so the groups are ordered
    with respect to each other and the entries within one are not: they
    are mutually independent, and taking them in the order recorded is
    as good as any other.
    """
    payload: dict[str, Any] = json.loads(path.read_text())
    return [list(group) for group in payload["order"]]


def next_subclause(
    order: list[list[str]], issues: list[dict[str, Any]],
) -> tuple[str, int] | None:
    """Return the earliest subclause in *order* an open issue tracks.

    Matching is on the canonical issue title for the subclause and
    nothing else. An issue merely *mentioning* a subclause is not
    tracking it — the work files such issues routinely, naming a clause
    in a title to say what a defect is about — and treating a mention as
    a tracking issue would send the campaign to a subclause that nobody
    had opened work on.

    Returns ``None`` where no subclause in the order has one, which is
    the campaign having nothing left to take rather than an error.
    """
    by_title = {
        str(issue["title"]): int(issue["number"]) for issue in issues
    }
    for group in order:
        for subclause in group:
            number = by_title.get(issue_title_for(subclause))
            if number is not None:
                return subclause, number
    return None
