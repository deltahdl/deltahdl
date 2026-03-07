"""Shared argparse and command-building helpers for classify scripts."""

import argparse


def add_output_args(parser: argparse.ArgumentParser) -> None:
    """Add --output-dir, --lrm, and --max-lines arguments."""
    parser.add_argument(
        "--output-dir", required=True,
        help="Directory for output files",
    )
    parser.add_argument(
        "--lrm", required=True,
        help="Path to IEEE 1800-2023 LRM PDF",
    )
    parser.add_argument(
        "--max-lines", type=int, required=True,
        help="Maximum lines per output file",
    )


def add_github_args(parser: argparse.ArgumentParser) -> None:
    """Add --organization and --repo arguments."""
    parser.add_argument(
        "--organization", required=True,
        help="GitHub organization for the issue",
    )
    parser.add_argument(
        "--repo", required=True,
        help="GitHub repository for the issue",
    )


def add_run_mode_args(parser: argparse.ArgumentParser) -> None:
    """Add --dry-run and --no-commit arguments."""
    parser.add_argument(
        "--dry-run", action="store_true",
        help="Classify only, don't write files",
    )
    parser.add_argument(
        "--no-commit", action="store_true",
        help="Skip git commit and push",
    )


def append_classify_cmd_flags(
    cmd: list[str], args: argparse.Namespace,
) -> None:
    """Append common classify flags to a subprocess command."""
    cmd += [
        "--output-dir", args.output_dir,
        "--lrm", args.lrm,
        "--organization", args.organization,
        "--repo", args.repo,
        "--max-lines", str(args.max_lines),
    ]
    if args.dry_run:
        cmd.append("--dry-run")
    if args.no_commit:
        cmd.append("--no-commit")
