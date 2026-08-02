"""The files a length cap admits, and the ones it does not.

A cap on how long a source file may grow is enforced by a step that walks the
tree, counts, and fails. That step stands in front of everything downstream of
it, which is what makes the cap everybody's to keep: a file over the line holds
back the build, the tests and every tier behind them, so it is fixed rather
than accumulated. The cost of that arrangement is that the breach and the
silence it causes arrive together, and a run reporting nothing but the cap
looks the same as a run in which nothing else was ever asked.

The walk here is the same walk, made available where it can be run and reported
apart from the gate it mirrors. A tree that has grown a file past the cap then
says so in a run that is green but for that, naming the file, while the gate
goes on holding back what it holds back.

Lines are counted the way the shell counts them, by the newlines a file ends
its lines with, because a breach has to be reported against the same number the
gate compared. A cap is not restated here either: it is read out of the step
that enforces it, so the gate and the walk cannot come to hold two different
limits. :func:`steps_of` takes a workflow apart into the steps of each job and
:func:`line_caps` reads, from the steps that count lines, the number each one
compares against.
"""

import re
from pathlib import Path
from typing import Any

import yaml

Step = dict[str, Any]

# A step enforces a length cap by counting a file's lines and comparing the
# count against a number written into the step. Reading the number there is
# what keeps one statement of the limit: a walk that mirrors the gate from
# somewhere else and carries its own copy stops mirroring it the moment either
# copy is changed alone.
COUNTS_LINES = "wc -l"
_CAP = re.compile(r'-gt\s+"?(\d+)"?')


def steps_of(text: str) -> dict[str, list[Step]]:
    """Return the steps of every job in the workflow *text*, by job name."""
    parsed: Any = yaml.safe_load(text)
    return {
        str(name): list(job.get("steps", []))
        for name, job in parsed["jobs"].items()
    }


def line_caps(steps: list[Step]) -> list[int]:
    """Return every file-length cap *steps* enforce by counting lines."""
    found: set[int] = set()
    for step in steps:
        script = str(step.get("run", ""))
        if COUNTS_LINES in script:
            found.update(int(cap) for cap in _CAP.findall(script))
    return sorted(found)


def line_count(path: Path) -> int:
    """Return the number of newline-terminated lines *path* holds."""
    return path.read_bytes().count(b"\n")


def sources_under(root: Path, suffixes: tuple[str, ...]) -> list[Path]:
    """Return every file under *root* whose name ends in one of *suffixes*."""
    return sorted(
        found
        for found in root.rglob("*")
        if found.is_file() and found.suffix in suffixes
    )


def over_limit(
    roots: tuple[Path, ...], limit: int, suffixes: tuple[str, ...]
) -> list[tuple[Path, int]]:
    """Return each file under *roots* longer than *limit*, with its length."""
    too_long: list[tuple[Path, int]] = []
    for root in roots:
        for found in sources_under(root, suffixes):
            lines = line_count(found)
            if lines > limit:
                too_long.append((found, lines))
    return sorted(too_long)
