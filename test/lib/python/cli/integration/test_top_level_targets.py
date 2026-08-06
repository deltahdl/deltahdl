"""Tests that --subclause admits every target with no dot in its name.

``lib.python.cli`` decides which identifiers ``--subclause`` accepts, and
``generate_lrm_subclause_dependencies`` decides which identifiers the
campaign hands it: it walks the LRM once and writes every satisfaction
target to ``docs/dependency_graph.json``. Nearly every target is a
subclause and carries a dot, but the walk also yields the entries that
have nothing numbered beneath them, and those are named by a bare number
or a bare letter.

The two sides are read together here because neither one can see the
mismatch alone. A unit test over ``SUBCLAUSE_RE`` asserts what the regex
was written to accept, and the recorded walk knows what has to be
accepted; tightening the regex to require a dot would leave both halves
passing while the campaign silently skipped those entries.

``docs/dependency_graph.json`` stands in for the table of contents
itself, which lives in the LRM PDF and is not committed. It is the walk's
own record of the same document.
"""

import argparse
import json
from pathlib import Path

from lib.python.cli import (
    add_lrm_arg,
    add_subclause_arg,
    parse_and_validate_subclause,
)

GRAPH_PATH = (
    Path(__file__).resolve().parents[5] / "docs" / "dependency_graph.json"
)


def _undotted_targets() -> list[str]:
    """Return the recorded targets whose identifiers carry no dot."""
    payload: dict[str, dict[str, object]] = json.loads(GRAPH_PATH.read_text())
    return [target for target in payload["records"] if "." not in target]


def _rejects(target: str, lrm: Path) -> bool:
    """Return whether --subclause turns *target* away."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    try:
        parse_and_validate_subclause(
            parser, ["--lrm", str(lrm), "--subclause", target],
        )
    except SystemExit:
        return True
    return False


def test_recorded_walk_holds_undotted_targets() -> None:
    """The recorded walk holds at least one target with no dot.

    Without this the check below passes over an empty list and says
    nothing about what --subclause admits.
    """
    assert _undotted_targets() != []


def test_every_undotted_target_is_accepted(tmp_path: Path) -> None:
    """--subclause accepts every recorded target that carries no dot."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    rejected = [t for t in _undotted_targets() if _rejects(t, lrm)]
    assert rejected == []
