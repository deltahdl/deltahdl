import argparse
from pathlib import Path


def add_lrm_arg(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the LRM PDF.",
    )


def add_model_arg(
    parser: argparse.ArgumentParser, *, default: str = "opus",
) -> None:
    parser.add_argument(
        "--model",
        type=str,
        default=default,
        help=f"Claude model to use (default: {default}).",
    )


def add_effort_arg(
    parser: argparse.ArgumentParser, *, default: str = "medium",
) -> None:
    parser.add_argument(
        "--effort",
        type=str,
        default=default,
        choices=["low", "medium", "high", "xhigh", "max"],
        help=f"Claude CLI thinking-effort level (default: {default}).",
    )


def validate_lrm(parser: argparse.ArgumentParser, args: argparse.Namespace) -> None:
    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")


def parse_and_validate(
    parser: argparse.ArgumentParser, argv: list[str] | None = None,
) -> argparse.Namespace:
    args = parser.parse_args(argv)
    validate_lrm(parser, args)
    return args
