#!/usr/bin/env python3
"""Dispatch LRM clause implementation prompts by clause depth."""

import argparse
import re
from pathlib import Path

from . import prompt_v, prompt_v_w, prompt_v_w_x, prompt_v_w_x_y, prompt_v_w_x_y_z
from .common import run_classify_tests_in_file, run_prompt


CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")

_HANDLERS = {
    1: prompt_v,
    2: prompt_v_w,
    3: prompt_v_w_x,
    4: prompt_v_w_x_y,
    5: prompt_v_w_x_y_z,
}


def parse_args(argv=None):
    """Parse command-line arguments for clause implementation."""
    parser = argparse.ArgumentParser(
        description="Generate an implementation prompt for a given LRM clause.",
    )
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the LRM text file.",
    )
    parser.add_argument(
        "--clause",
        type=str,
        required=True,
        help="LRM clause number (V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z).",
    )
    parser.add_argument(
        "--issue",
        type=int,
        required=True,
        help="GitHub Issue number to read and correct after implementation.",
    )
    parser.add_argument(
        "--model",
        type=str,
        default="sonnet",
        help="Claude model to use (default: sonnet).",
    )
    args = parser.parse_args(argv)

    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")

    if not CLAUSE_RE.match(args.clause):
        parser.error(
            f"Invalid clause format '{args.clause}'. "
            "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "(V is a number or uppercase letter; remaining parts are numbers)."
        )

    return args


def clause_depth(clause: str) -> int:
    """Return the nesting depth of a clause string."""
    return clause.count(".") + 1


def main(argv=None):
    """Parse args, dispatch to the depth-appropriate prompt, and invoke Claude."""
    args = parse_args(argv)
    depth = clause_depth(args.clause)
    handler = _HANDLERS[depth]

    run_prompt(
        handler.build_prompt, args.lrm, args.clause,
        issue=args.issue, model=args.model,
    )
    run_classify_tests_in_file(args.lrm)


if __name__ == "__main__":
    main()
