"""Tests for lib.classify."""

import argparse

from lib.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
)


# --- add_output_args ---


def test_add_output_args_adds_output_dir() -> None:
    """Adds --output-dir argument."""
    parser = argparse.ArgumentParser()
    add_output_args(parser)
    args = parser.parse_args(["--output-dir", "/tmp", "--lrm", "f", "--max-lines", "5"])
    assert args.output_dir == "/tmp"


def test_add_output_args_adds_lrm() -> None:
    """Adds --lrm argument."""
    parser = argparse.ArgumentParser()
    add_output_args(parser)
    args = parser.parse_args(["--output-dir", "/tmp", "--lrm", "lrm.txt", "--max-lines", "5"])
    assert args.lrm == "lrm.txt"


def test_add_output_args_adds_max_lines() -> None:
    """Adds --max-lines argument as int."""
    parser = argparse.ArgumentParser()
    add_output_args(parser)
    args = parser.parse_args(["--output-dir", "/tmp", "--lrm", "f", "--max-lines", "42"])
    assert args.max_lines == 42


# --- add_github_args ---


def test_add_github_args_adds_organization() -> None:
    """Adds --organization argument."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--organization", "myorg", "--repo", "myrepo"])
    assert args.organization == "myorg"


def test_add_github_args_adds_repo() -> None:
    """Adds --repo argument."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--organization", "myorg", "--repo", "myrepo"])
    assert args.repo == "myrepo"


# --- add_run_mode_args ---


def test_add_run_mode_args_dry_run_default_false() -> None:
    """--dry-run defaults to False."""
    parser = argparse.ArgumentParser()
    add_run_mode_args(parser)
    args = parser.parse_args([])
    assert args.dry_run is False


def test_add_run_mode_args_dry_run_set() -> None:
    """--dry-run sets to True."""
    parser = argparse.ArgumentParser()
    add_run_mode_args(parser)
    args = parser.parse_args(["--dry-run"])
    assert args.dry_run is True


def test_add_run_mode_args_no_commit_default_false() -> None:
    """--no-commit defaults to False."""
    parser = argparse.ArgumentParser()
    add_run_mode_args(parser)
    args = parser.parse_args([])
    assert args.no_commit is False


def test_add_run_mode_args_no_commit_set() -> None:
    """--no-commit sets to True."""
    parser = argparse.ArgumentParser()
    add_run_mode_args(parser)
    args = parser.parse_args(["--no-commit"])
    assert args.no_commit is True
