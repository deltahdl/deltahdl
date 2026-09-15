import json
from pathlib import Path
from typing import Any

from lib.python.github import issue_title_for


def load_order(path: Path) -> list[list[str]]:
    payload: dict[str, Any] = json.loads(path.read_text())
    return [list(group) for group in payload["order"]]


def next_subclause(
    order: list[list[str]], issues: list[dict[str, Any]],
) -> tuple[str, int] | None:
    by_title = {
        str(issue["title"]): int(issue["number"]) for issue in issues
    }
    for group in order:
        for subclause in group:
            number = by_title.get(issue_title_for(subclause))
            if number is not None:
                return subclause, number
    return None
