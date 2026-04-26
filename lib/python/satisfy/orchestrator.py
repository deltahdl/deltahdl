"""Shared infrastructure for the satisfaction-pipeline orchestrators.

The two orchestrators (``satisfy_subclause`` and the inner
``satisfy_unsatisfied_subclause``) share two pieces of plumbing: the
``--in-progress`` cycle-tracking flag, and a small helper that runs a
subprocess for stdout while exiting on a non-zero return code. They
live here so the orchestrators do not duplicate them.
"""

import argparse
import subprocess
import sys


def add_in_progress_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--in-progress`` argument used for cycle detection."""
    parser.add_argument(
        "--in-progress",
        type=str,
        default="",
        help=(
            "Comma-separated subclauses currently in progress in the"
            " caller stack. Used for cycle detection."
        ),
    )


def parse_in_progress(raw: str) -> list[str]:
    """Split a comma-separated --in-progress value into a list."""
    return [item.strip() for item in raw.split(",") if item.strip()]


def run_capture(cmd: list[str]) -> str:
    """Run *cmd*, return its stdout, exit non-zero on failure."""
    completed = subprocess.run(
        cmd, capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return completed.stdout
