"""End-to-end tests for the next_subclause command line.

These run the script the way a caller runs it — as a subprocess, with
``gh`` resolved off the path — so the wiring between the entry point, the
listing and the printed line is exercised rather than stubbed.
"""

import subprocess
from collections.abc import Callable
from pathlib import Path


def test_cli_prints_the_tracked_subclause_and_its_issue(
    run_cli: Callable[..., subprocess.CompletedProcess[str]],
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    """The whole chain answers with one line naming subclause and issue."""
    completed = run_cli(
        write_graph([["3.1"], ["3.2"]]),
        [{"number": 42, "title": "Satisfy IEEE 1800-2023 §3.2"}],
    )
    assert completed.stdout == "§3.2 #42\n"


def test_cli_exits_nonzero_when_nothing_is_tracked(
    run_cli: Callable[..., subprocess.CompletedProcess[str]],
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    """An empty listing leaves nothing to take, and the exit code says so."""
    assert run_cli(write_graph([["3.1"]]), []).returncode == 1
