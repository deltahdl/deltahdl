"""Unit tests for main-flow functions in split_tests."""

import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import split_tests
from helpers import make_parsed_file as _parsed
from helpers import make_test_block as _tb
from helpers import stub_classifier

_parse_args = getattr(split_tests, "_parse_args")
_print_classification_table = getattr(
    split_tests, "_print_classification_table",
)
_print_dry_run_summary = getattr(split_tests, "_print_dry_run_summary")
_group_tests = getattr(split_tests, "_group_tests")
_resolve_destinations = getattr(split_tests, "_resolve_destinations")
_write_files = getattr(split_tests, "_write_files")
_run = getattr(split_tests, "_run")


def _make_input_file(tmp_path):
    """Create a minimal test input file and return its path."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n}\n",
        encoding="utf-8",
    )
    return f


def _parser_response():
    """Return a standard classifier response for test_parser_ clause 6.1."""
    return {
        "tests": [{"test_name": "T", "prefix": "test_parser_",
                    "clause": "6.1", "rationale": "r"}],
    }


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_basic(monkeypatch):
    """Parses --file, --output-dir, and --dry-run."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out"],
    )
    args = _parse_args()
    assert args.file == "f.cpp" and not args.dry_run


def test_parse_args_dry_run(monkeypatch):
    """Parses --dry-run flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out", "--dry-run"],
    )
    assert _parse_args().dry_run is True


# ---- _print_classification_table -------------------------------------------


def test_print_classification_table_output(capsys):
    """Prints a formatted table of classifications."""
    t = _tb("T", prefix="test_parser_", clause="6.1", rationale="r")
    _print_classification_table([t])
    out = capsys.readouterr().out
    assert "test_parser_" in out and "6.1" in out


# ---- _print_dry_run_summary ------------------------------------------------


def test_print_dry_run_summary_merge(tmp_path, capsys):
    """MERGE line is printed for merge targets."""
    t = _tb("M", prefix="test_parser_", clause="6.1")
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    _print_dry_run_summary([], [(merge_path, [t])])
    assert "MERGE" in capsys.readouterr().out


def test_print_dry_run_summary_nothing(capsys):
    """'Nothing to do' is printed when both lists are empty."""
    _print_dry_run_summary([], [])
    assert "already located in the correct files" in capsys.readouterr().out


# ---- _group_tests ----------------------------------------------------------


def test_group_tests_normal():
    """Groups tests by (prefix, clause)."""
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    groups = _group_tests([t1, t2])
    assert len(groups[("test_parser_", "6.1")]) == 2


def test_group_tests_defaults():
    """Uses defaults when prefix/clause are None."""
    t = _tb("A")
    groups = _group_tests([t])
    assert ("test_non_lrm", "non-lrm") in groups


# ---- _resolve_destinations -------------------------------------------------


def test_resolve_destinations_create(tmp_path):
    """Creates new files when no merge target exists."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    to_create, to_merge = _resolve_destinations(
        groups, tmp_path, {},
    )
    assert len(to_create) == 1 and len(to_merge) == 0


def test_resolve_destinations_merge(tmp_path):
    """Merges into existing file."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "TEST(S, Old) {}\n",
    )
    t = _tb("New", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    _, to_merge = _resolve_destinations(
        groups, tmp_path, {},
    )
    assert len(to_merge) == 1


def test_resolve_destinations_duplicates(tmp_path):
    """Drops duplicate tests."""
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    to_create, to_merge = _resolve_destinations(
        groups, tmp_path, {},
    )
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_all_dupes(tmp_path, capsys):
    """Prints 'All tests are duplicates' when all are dupes."""
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    _resolve_destinations(groups, tmp_path, {})
    assert "All tests for 6.1 are duplicates" in capsys.readouterr().out


def test_resolve_destinations_excludes_source(tmp_path):
    """Source file matching target is skipped (already correct)."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text("TEST(S, Self) {\n}\n")
    t = _tb("Self", prefix="test_non_lrm_", clause="non-lrm:aig")
    groups = {("test_non_lrm_", "non-lrm:aig"): [t]}
    to_create, to_merge = _resolve_destinations(
        groups, tmp_path, {}, exclude_path=src,
    )
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_source_is_target(tmp_path):
    """Tests already in the correct file are skipped, not recreated."""
    src = tmp_path / "test_non_lrm_vpi.cpp"
    src.write_text("TEST(S, Keep) {\n}\n")
    t = _tb("Keep", prefix="test_non_lrm_", clause="non-lrm:vpi")
    groups = {("test_non_lrm_", "non-lrm:vpi"): [t]}
    to_create, _ = _resolve_destinations(
        groups, tmp_path, {}, exclude_path=src,
    )
    assert len(to_create) == 0


def test_resolve_destinations_source_is_target_reports_skip(tmp_path, capsys):
    """Skip message is printed when source matches target."""
    src = tmp_path / "test_non_lrm_vpi.cpp"
    src.write_text("TEST(S, Keep) {\n}\n")
    t = _tb("Keep", prefix="test_non_lrm_", clause="non-lrm:vpi")
    groups = {("test_non_lrm_", "non-lrm:vpi"): [t]}
    _resolve_destinations(groups, tmp_path, {}, exclude_path=src)
    assert "already in" in capsys.readouterr().out


# ---- _write_files ----------------------------------------------------------


def test_write_files_create(tmp_path):
    """Creates new files on disk."""
    t = _tb("T", comments=[])
    parsed = _parsed()
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    names = _write_files(
        to_create, [], parsed, tmp_path, {},
    )
    assert "test_parser_clause_06_01" in names


def test_write_files_merge(tmp_path):
    """Merges tests into existing files."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\nTEST(S, Old) {\n}\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("New", comments=[])
    parsed = _parsed()
    names = _write_files(
        [], [(f, [t])], parsed, tmp_path, {},
    )
    assert not names


# ---- _run ------------------------------------------------------------------


def test_run_file_not_found(tmp_path):
    """Exits when input file does not exist."""
    args = SimpleNamespace(
        file=str(tmp_path / "missing.cpp"),
        output_dir=str(tmp_path),
        dry_run=False,
    )
    with pytest.raises(SystemExit):
        _run(args)


def test_run_no_test_blocks(tmp_path):
    """Exits when file has no TEST blocks."""
    f = tmp_path / "empty.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\nint x = 0;\n",
        encoding="utf-8",
    )
    args = SimpleNamespace(
        file=str(f), output_dir=str(tmp_path), dry_run=False,
    )
    with pytest.raises(SystemExit):
        _run(args)


def test_run_dry_run(tmp_path, monkeypatch, capsys):
    """Dry run classifies but does not write files."""
    f = _make_input_file(tmp_path)
    stub_classifier(monkeypatch, tmp_path, _parser_response())
    args = SimpleNamespace(
        file=str(f), output_dir=str(tmp_path), dry_run=True,
    )
    _run(args)
    assert "DRY RUN complete" in capsys.readouterr().out


def test_run_live(tmp_path, monkeypatch, capsys):
    """Live run writes files, updates cmake, commits."""
    f = _make_input_file(tmp_path)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n",
        encoding="utf-8",
    )
    standalone = tmp_path / "STANDALONE.md"
    standalone.write_text(
        "- [ ] test_input\n", encoding="utf-8",
    )
    stub_classifier(monkeypatch, tmp_path, _parser_response())
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    monkeypatch.setattr(split_tests, "STANDALONE_PATH", standalone)
    monkeypatch.setattr(
        subprocess, "run",
        lambda *_a, **_kw: MagicMock(returncode=0),
    )
    args = SimpleNamespace(
        file=str(f), output_dir=str(tmp_path), dry_run=False,
    )
    _run(args)
    assert "Done!" in capsys.readouterr().out


def test_run_live_self_named(tmp_path, monkeypatch):
    """Source file already in correct location is left untouched."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n\nTEST(S, T) {\n}\n",
        encoding="utf-8",
    )
    resp = {"tests": [{"test_name": "T", "prefix": "test_non_lrm_",
                        "clause": "non-lrm:aig", "rationale": "r"}]}
    stub_classifier(monkeypatch, tmp_path, resp)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text("# header\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    monkeypatch.setattr(
        split_tests, "STANDALONE_PATH", tmp_path / "no.md",
    )
    monkeypatch.setattr(
        subprocess, "run",
        lambda *_a, **_kw: MagicMock(returncode=0),
    )
    args = SimpleNamespace(
        file=str(src), output_dir=str(tmp_path), dry_run=False,
    )
    _run(args)
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


def test_run_live_mixed_keeps_source(tmp_path, monkeypatch):
    """Source kept when some tests stay and others go elsewhere."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, Stay) {\n}\n"
        "TEST(S, Move) {\n}\n",
        encoding="utf-8",
    )
    resp = {"tests": [
        {"test_name": "Stay", "prefix": "test_non_lrm_",
         "clause": "non-lrm:aig", "rationale": "r"},
        {"test_name": "Move", "prefix": "test_parser_",
         "clause": "6.1", "rationale": "r"},
    ]}
    stub_classifier(monkeypatch, tmp_path, resp)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text("# header\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    monkeypatch.setattr(
        split_tests, "STANDALONE_PATH", tmp_path / "no.md",
    )
    monkeypatch.setattr(
        subprocess, "run",
        lambda *_a, **_kw: MagicMock(returncode=0),
    )
    args = SimpleNamespace(
        file=str(src), output_dir=str(tmp_path), dry_run=False,
    )
    _run(args)
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


# ---- main ------------------------------------------------------------------


def test_main(tmp_path, monkeypatch):
    """main sets up logging and calls _run."""
    monkeypatch.setattr(Path, "home", staticmethod(lambda: tmp_path))
    ran = [False]

    def mock_run(_args):
        ran[0] = True

    monkeypatch.setattr(split_tests, "_run", mock_run)
    monkeypatch.setattr(
        split_tests, "_parse_args",
        lambda: SimpleNamespace(
            file="x", output_dir="/tmp", dry_run=True,
        ),
    )
    split_tests.main()
    assert ran[0] is True
