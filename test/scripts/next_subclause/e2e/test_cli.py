import subprocess
from collections.abc import Callable
from pathlib import Path


def test_cli_prints_the_tracked_subclause_and_its_issue(
    run_cli: Callable[..., subprocess.CompletedProcess[str]],
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    completed = run_cli(
        write_graph([["3.1"], ["3.2"]]),
        [{"number": 42, "title": "Satisfy IEEE 1800-2023 §3.2"}],
    )
    assert completed.stdout == "§3.2 #42\n"


def test_cli_exits_nonzero_when_nothing_is_tracked(
    run_cli: Callable[..., subprocess.CompletedProcess[str]],
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    assert run_cli(write_graph([["3.1"]]), []).returncode == 1
