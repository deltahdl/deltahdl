"""Tests for lib.classify."""

import argparse

from lib.python.classify import (
    STAGE_TO_PREFIX,
    add_github_args,
    add_output_args,
    add_run_mode_args,
    append_classify_cmd_flags,
    build_hierarchy,
    build_lrm_read_instruction,
    clause_to_filename,
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


# --- STAGE_TO_PREFIX ---


def test_stage_to_prefix_has_all_stages() -> None:
    """Contains all six pipeline stages."""
    assert set(STAGE_TO_PREFIX) == {
        "preprocessor", "lexer", "parser",
        "elaborator", "simulator", "synthesizer",
    }


def test_stage_to_prefix_values_are_test_prefixes() -> None:
    """Every value starts with test_ and ends with _."""
    assert all(v.startswith("test_") and v.endswith("_") for v in STAGE_TO_PREFIX.values())


# --- clause_to_filename ---


def test_clause_to_filename_regular() -> None:
    """Regular clause becomes padded clause filename."""
    assert clause_to_filename("test_parser_", "6.1") == "test_parser_clause_06_01"


def test_clause_to_filename_non_lrm_with_topic() -> None:
    """Non-LRM with topic uses the topic."""
    assert clause_to_filename("test_non_lrm_", "non-lrm:aig") == "test_non_lrm_aig"


def test_clause_to_filename_non_lrm_no_topic() -> None:
    """Non-LRM without topic defaults to misc."""
    assert clause_to_filename("test_non_lrm_", "non-lrm") == "test_non_lrm_misc"


def test_clause_to_filename_bare_annex() -> None:
    """Single letter becomes bare annex filename."""
    assert clause_to_filename("test_parser_", "A") == "test_parser_annex_a"


def test_clause_to_filename_annex_subclause() -> None:
    """Annex subclause becomes padded annex filename."""
    assert clause_to_filename("test_parser_", "A.1.3") == "test_parser_annex_a_01_03"


# --- build_hierarchy ---


def test_build_hierarchy_numeric_depth_1() -> None:
    """Clause '4' produces depth-1 numeric hierarchy."""
    assert build_hierarchy("4")["clause_number"] == "4"


def test_build_hierarchy_numeric_no_ancestors() -> None:
    """Depth-2 clause '4.1' has no ancestors."""
    assert build_hierarchy("4.1")["ancestors"] == []


def test_build_hierarchy_numeric_ancestors() -> None:
    """Depth-3 clause '6.24.1' has one ancestor."""
    assert build_hierarchy("6.24.1")["ancestors"] == ["6.24"]


def test_build_hierarchy_annex_letter() -> None:
    """Annex 'B' sets letter to 'B'."""
    assert build_hierarchy("B")["letter"] == "B"


def test_build_hierarchy_annex_is_annex() -> None:
    """Annex 'A.8' is flagged as annex."""
    assert build_hierarchy("A.8")["is_annex"] is True


def test_build_hierarchy_numeric_not_annex() -> None:
    """Numeric '4' is not flagged as annex."""
    assert build_hierarchy("4")["is_annex"] is False


# --- build_lrm_read_instruction ---


def test_lrm_read_general_subclause() -> None:
    """General subclause (X.1) does not add 'Also read General'."""
    result = build_lrm_read_instruction("6.1", "/lrm.pdf")
    assert "Also read" not in result


def test_lrm_read_non_general_adds_context() -> None:
    """Non-general subclause adds 'Also read General or Overview'."""
    result = build_lrm_read_instruction("6.3", "/lrm.pdf")
    assert "General or Overview" in result


def test_lrm_read_deep_includes_ancestors() -> None:
    """Deep subclause includes ancestor list."""
    result = build_lrm_read_instruction("6.3.2", "/lrm.pdf")
    assert "§6.3" in result


def test_lrm_read_includes_lrm_path() -> None:
    """Instruction includes the LRM path."""
    result = build_lrm_read_instruction("4.1", "/my/lrm.pdf")
    assert "/my/lrm.pdf" in result


def test_lrm_read_includes_subclause() -> None:
    """Instruction includes the subclause number."""
    result = build_lrm_read_instruction("9.2.1", "/lrm.pdf")
    assert "§9.2.1" in result
