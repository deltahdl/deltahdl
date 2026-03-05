"""Tests for lib.classify."""

import argparse

from lib.python.classify import (
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
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


# --- append_classify_cmd_flags ---


_STUB_ARGS = argparse.Namespace(
    output_dir="/out", lrm="/lrm.txt",
    organization="org", repo="repo",
    max_lines=100, dry_run=False, no_commit=False,
)


def test_append_classify_cmd_flags_output_dir() -> None:
    """Appends --output-dir with correct value."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    idx = cmd.index("--output-dir")
    assert cmd[idx + 1] == "/out"


def test_append_classify_cmd_flags_lrm() -> None:
    """Appends --lrm with correct value."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    idx = cmd.index("--lrm")
    assert cmd[idx + 1] == "/lrm.txt"


def test_append_classify_cmd_flags_organization() -> None:
    """Appends --organization with correct value."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    idx = cmd.index("--organization")
    assert cmd[idx + 1] == "org"


def test_append_classify_cmd_flags_repo() -> None:
    """Appends --repo with correct value."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    idx = cmd.index("--repo")
    assert cmd[idx + 1] == "repo"


def test_append_classify_cmd_flags_max_lines() -> None:
    """Appends --max-lines as string."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    idx = cmd.index("--max-lines")
    assert cmd[idx + 1] == "100"


def test_append_classify_cmd_flags_dry_run_included() -> None:
    """Appends --dry-run when set."""
    args = argparse.Namespace(**{**_STUB_ARGS.__dict__, "dry_run": True})
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, args)
    assert "--dry-run" in cmd


def test_append_classify_cmd_flags_dry_run_omitted() -> None:
    """Omits --dry-run when not set."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    assert "--dry-run" not in cmd


def test_append_classify_cmd_flags_no_commit_included() -> None:
    """Appends --no-commit when set."""
    args = argparse.Namespace(**{**_STUB_ARGS.__dict__, "no_commit": True})
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, args)
    assert "--no-commit" in cmd


def test_append_classify_cmd_flags_no_commit_omitted() -> None:
    """Omits --no-commit when not set."""
    cmd: list[str] = []
    append_classify_cmd_flags(cmd, _STUB_ARGS)
    assert "--no-commit" not in cmd
