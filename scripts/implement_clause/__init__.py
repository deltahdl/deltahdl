#!/usr/bin/env python3
"""Dispatch LRM clause implementation prompts by clause depth."""

import argparse
import re
from pathlib import Path


CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


def parse_args(argv=None):
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
    return clause.count(".") + 1


def main(argv=None):
    args = parse_args(argv)
    depth = clause_depth(args.clause)

    if depth == 1:
        from . import prompt_v as handler
    elif depth == 2:
        from . import prompt_v_w as handler
    elif depth == 3:
        from . import prompt_v_w_x as handler
    elif depth == 4:
        from . import prompt_v_w_x_y as handler
    else:
        from . import prompt_v_w_x_y_z as handler

    handler.run(args.lrm, args.clause, issue=args.issue, model=args.model)

    from .common import run_classify_tests_in_file
    run_classify_tests_in_file(args.lrm)


if __name__ == "__main__":
    main()
