import argparse
import re
from pathlib import Path

_CLAUSE_RE = re.compile(
    r"^([1-9][0-9]*|[A-Z])"  # V: positive non-zero integer or uppercase letter
    r"(\.[0-9]+){0,4}$"      # optional .W, .W.X, .W.X.Y, .W.X.Y.Z
)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        description="Convert figures from the IEEE 1800-2023 SystemVerilog LRM.",
    )
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the IEEE 1800-2023 SystemVerilog LRM.",
    )
    parser.add_argument(
        "--clause",
        required=True,
        help="LRM clause (e.g. 6, 6.3, 6.3.1, A, A.1.2).",
    )
    args = parser.parse_args(argv)
    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")
    if not _CLAUSE_RE.match(args.clause):
        parser.error(
            f"Invalid clause '{args.clause}'. "
            "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "where V is a positive non-zero number or uppercase letter."
        )
    return args
