"""Shared utilities for test runner scripts."""

import os
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
BINARY = REPO_ROOT / "build" / "src" / "deltahdl"

_NO_COLOR = (
    not sys.stdout.isatty() and not os.environ.get("CI")
) or os.environ.get("NO_COLOR")

GREEN = "" if _NO_COLOR else "\033[32m"
RED = "" if _NO_COLOR else "\033[31m"
RESET = "" if _NO_COLOR else "\033[0m"


def print_result(passed, name):
    """Print a colored PASS/FAIL line for a single test."""
    if passed:
        print(f"  {GREEN}PASS{RESET}: {name}", flush=True)
    else:
        print(f"  {RED}FAIL{RESET}: {name}", flush=True)
