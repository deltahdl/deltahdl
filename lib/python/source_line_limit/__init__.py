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
gate compared. A cap is not restated here: it is passed in, read from the step
that enforces it, so the two cannot drift apart.
"""

from pathlib import Path


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
