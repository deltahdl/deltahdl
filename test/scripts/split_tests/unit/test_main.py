"""Unit tests for main-flow functions in split_tests."""

import sys
from types import SimpleNamespace

import pytest

import split_tests
from helpers import make_parsed_file as _parsed
from helpers import make_test_block as _tb
from helpers import stub_classifier

_parse_args = getattr(split_tests, "_parse_args")
_format_clause = getattr(split_tests, "_format_clause")
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
    """Return a standard single-test classifier response."""
    return {
        "prefix": "test_parser_",
        "clause": "6.1", "rationale": "r",
    }


def _run_args(tmp_path, **overrides):
    """Build a SimpleNamespace with all required _run args."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "dry_run": False,
        "lrm": str(tmp_path / "lrm.txt"),
        "arch": str(tmp_path / "arch.md"),
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_basic(monkeypatch):
    """Parses --file, --output-dir, --lrm, and --arch."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--arch", "/arch.md"],
    )
    args = _parse_args()
    assert args.file == "f.cpp" and not args.dry_run


def test_parse_args_dry_run(monkeypatch):
    """Parses --dry-run flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--arch", "/arch.md", "--dry-run"],
    )
    assert _parse_args().dry_run is True


def test_parse_args_lrm(monkeypatch):
    """Parses --lrm flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/my/LRM.txt", "--arch", "/arch.md"],
    )
    assert _parse_args().lrm == "/my/LRM.txt"


def test_parse_args_arch(monkeypatch):
    """Parses --arch flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--arch", "/my/ARCH.md"],
    )
    assert _parse_args().arch == "/my/ARCH.md"


# ---- _format_clause --------------------------------------------------------


def test_format_clause_non_lrm():
    """Non-LRM clause formats as 'Non-LRM: TAG'."""
    assert _format_clause("non-lrm:aig") == "Non-LRM: AIG"


def test_format_clause_non_lrm_underscore():
    """Non-LRM clause with underscore converts to space."""
    assert _format_clause("non-lrm:aig_opt") == "Non-LRM: AIG OPT"


def test_format_clause_regular():
    """Regular clause formats with section sign."""
    assert _format_clause("6.1") == "\u00a76.1"


# ---- _print_classification_table -------------------------------------------


def test_print_classification_table_output(capsys):
    """Prints a formatted table with test name and clause."""
    t = _tb("T", prefix="test_parser_", clause="6.1", rationale="r")
    _print_classification_table([t])
    out = capsys.readouterr().out
    assert "T()" in out and "\u00a76.1" in out


def test_print_classification_table_non_lrm_shows_tag(capsys):
    """Non-LRM clause displays as 'Non-LRM: AIG'."""
    t = _tb("T", prefix="test_non_lrm_", clause="non-lrm:aig")
    _print_classification_table([t])
    assert "Non-LRM: AIG" in capsys.readouterr().out


def test_print_classification_table_non_lrm_no_section_sign(capsys):
    """Non-LRM clause does not use section sign."""
    t = _tb("T", prefix="test_non_lrm_", clause="non-lrm:aig")
    _print_classification_table([t])
    assert "\u00a7non-lrm" not in capsys.readouterr().out


def test_print_classification_table_box_top(capsys):
    """Table has unicode top-left corner."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "\u250c" in capsys.readouterr().out


def test_print_classification_table_box_sides(capsys):
    """Table has unicode vertical lines."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "\u2502" in capsys.readouterr().out


def test_print_classification_table_box_bottom(capsys):
    """Table has unicode bottom-left corner."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "\u2514" in capsys.readouterr().out


def test_print_classification_table_parentheses(capsys):
    """Test names include parentheses."""
    t = _tb("Foo", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "Foo()" in capsys.readouterr().out


def test_print_classification_table_row_separators(capsys):
    """Multi-row table has separator lines between each row."""
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    _print_classification_table([t1, t2])
    out = capsys.readouterr().out
    assert out.count("\u251c") == 2


# ---- _print_summary / _print_dry_run_summary ------------------------------


def test_print_summary_created(capsys):
    """Live summary prints '- Created'."""
    _print_summary = getattr(split_tests, "_print_summary")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    assert "- Created test_parser_clause_06_01.cpp" in capsys.readouterr().out


def test_print_summary_moved(capsys):
    """Live summary prints '- Moved'."""
    _print_summary = getattr(split_tests, "_print_summary")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    assert "- Moved 1 test(s)" in capsys.readouterr().out


def test_print_summary_deleted(capsys):
    """Live summary prints 'Deleted' when source_is_target is False."""
    _print_summary = getattr(split_tests, "_print_summary")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    out = capsys.readouterr().out
    assert "- Deleted test_input.cpp" in out


def test_print_summary_kept(capsys):
    """Live summary prints 'Kept' when source_is_target with n_kept."""
    _print_summary = getattr(split_tests, "_print_summary")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", True, n_kept=3)
    out = capsys.readouterr().out
    assert "- Kept 3 tests" in out


def test_print_summary_all_correct(capsys):
    """Live summary prints conclusion line."""
    _print_summary = getattr(split_tests, "_print_summary")
    _print_summary([], [], "test_input", True)
    assert "Summary: all already in correct file." in capsys.readouterr().out


def test_print_dry_run_summary_moved(tmp_path, capsys):
    """Dry-run prints '- Would have moved'."""
    t = _tb("M", prefix="test_parser_", clause="6.1")
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    _print_dry_run_summary(
        [], [(merge_path, [t])], "test_input", False,
    )
    assert "- Would have moved" in capsys.readouterr().out


def test_print_dry_run_summary_no_bare_moved(tmp_path, capsys):
    """Dry-run does not contain bare 'Moved' without 'Would have'."""
    t = _tb("M", prefix="test_parser_", clause="6.1")
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    _print_dry_run_summary(
        [], [(merge_path, [t])], "test_input", False,
    )
    out = capsys.readouterr().out
    assert "Moved" not in out.replace("Would have moved", "")


def test_print_dry_run_summary_create(capsys):
    """Dry-run prints 'Would have created'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_dry_run_summary(
        to_create, [], "test_input", False,
    )
    out = capsys.readouterr().out
    assert "- Would have created" in out


def test_print_dry_run_summary_deleted(capsys):
    """Dry-run prints 'Would have deleted'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_dry_run_summary(
        to_create, [], "test_input", False,
    )
    out = capsys.readouterr().out
    assert "- Would have deleted test_input.cpp" in out


def test_print_dry_run_summary_updated(capsys):
    """Dry-run prints 'Would have updated CMakeLists.txt'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_dry_run_summary(
        to_create, [], "test_input", False,
    )
    out = capsys.readouterr().out
    assert "- Would have updated CMakeLists.txt" in out


def test_print_dry_run_summary_kept(capsys):
    """Dry-run prints 'Would have kept'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_dry_run_summary(
        to_create, [], "test_input", True, n_kept=3,
    )
    out = capsys.readouterr().out
    assert "- Would have kept 3 tests" in out


def test_print_dry_run_summary_nothing(capsys):
    """Dry-run prints conclusion line when nothing to do."""
    _print_dry_run_summary([], [], "test_input", True)
    assert "Summary: all already in correct file." in capsys.readouterr().out


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
        groups, tmp_path,
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
        groups, tmp_path,
    )
    assert len(to_merge) == 1


def test_resolve_destinations_duplicates(tmp_path):
    """Drops duplicate tests."""
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    to_create, to_merge = _resolve_destinations(
        groups, tmp_path,
    )
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_all_dupes(tmp_path, capsys):
    """Prints removal message with parentheses for each duplicate."""
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    _resolve_destinations(groups, tmp_path)
    assert "- Removed T()" in capsys.readouterr().out


def test_resolve_destinations_dry_run_would_have_removed(
    tmp_path, capsys,
):
    """Dry-run prints 'Would have removed' with parentheses."""
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    _resolve_destinations(groups, tmp_path, dry_run=True)
    assert "- Would have removed T()" in capsys.readouterr().out


def test_resolve_destinations_excludes_source(tmp_path):
    """Source file matching target is skipped (already correct)."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text("TEST(S, Self) {\n}\n")
    t = _tb("Self", prefix="test_non_lrm_", clause="non-lrm:aig")
    groups = {("test_non_lrm_", "non-lrm:aig"): [t]}
    to_create, to_merge = _resolve_destinations(
        groups, tmp_path, exclude_path=src,
    )
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_source_is_target(tmp_path):
    """Tests already in the correct file are skipped, not recreated."""
    src = tmp_path / "test_non_lrm_vpi.cpp"
    src.write_text("TEST(S, Keep) {\n}\n")
    t = _tb("Keep", prefix="test_non_lrm_", clause="non-lrm:vpi")
    groups = {("test_non_lrm_", "non-lrm:vpi"): [t]}
    to_create, _ = _resolve_destinations(
        groups, tmp_path, exclude_path=src,
    )
    assert len(to_create) == 0


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
    args = _run_args(tmp_path, file=str(tmp_path / "missing.cpp"))
    with pytest.raises(SystemExit):
        _run(args)


def test_run_no_test_blocks(tmp_path):
    """Exits when file has no TEST blocks."""
    f = tmp_path / "empty.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\nint x = 0;\n",
        encoding="utf-8",
    )
    args = _run_args(tmp_path, file=str(f))
    with pytest.raises(SystemExit):
        _run(args)


def test_run_dry_run(tmp_path, monkeypatch, capsys):
    """Dry run classifies but does not write files."""
    _make_input_file(tmp_path)
    stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "dry run" in capsys.readouterr().out


def _setup_live_run(tmp_path, monkeypatch):
    """Create input file, cmake, and stub classifier for a live run."""
    _make_input_file(tmp_path)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n",
        encoding="utf-8",
    )
    stub_classifier(monkeypatch, _parser_response())
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    return _run_args(tmp_path)


def test_run_live(tmp_path, monkeypatch, capsys):
    """Live run writes files and updates cmake."""
    args = _setup_live_run(tmp_path, monkeypatch)
    _run(args)
    assert "Updated CMakeLists.txt" in capsys.readouterr().out


def test_run_live_merge(tmp_path, monkeypatch, capsys):
    """Live run merging into existing file prints move summary."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    args = _setup_live_run(tmp_path, monkeypatch)
    _run(args)
    assert "Moved 1 test(s) to test_parser_clause_06_01.cpp" in \
        capsys.readouterr().out


def _mixed_classifier(prompt):
    """Return different classifications based on which test is in prompt."""
    if "Stay" in prompt:
        return {
            "prefix": "test_non_lrm_",
            "clause": "non-lrm:aig", "rationale": "r",
        }
    return {
        "prefix": "test_parser_",
        "clause": "6.1", "rationale": "r",
    }


def _run_live_non_lrm(tmp_path, monkeypatch, src_body, classifier):
    """Write source, stub externals, and run live pipeline."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(src_body, encoding="utf-8")
    monkeypatch.setattr(
        split_tests, "_call_claude", classifier,
    )
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        f"# header\nadd_unit_test({src.stem})\n", encoding="utf-8",
    )
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    _run(_run_args(tmp_path, file=str(src)))


def _self_named_classifier(_prompt):
    """Classify single test as non-lrm:aig."""
    return {
        "prefix": "test_non_lrm_",
        "clause": "non-lrm:aig", "rationale": "r",
    }


def test_run_live_self_named(tmp_path, monkeypatch):
    """Source file already in correct location is left untouched."""
    _run_live_non_lrm(
        tmp_path, monkeypatch,
        "#include <gtest/gtest.h>\n\nTEST(S, T) {\n}\n",
        _self_named_classifier,
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


_MIXED_BODY = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Stay) {\n}\n"
    "TEST(S, Move) {\n}\n"
)


def test_run_live_mixed_keeps_source(tmp_path, monkeypatch):
    """Source is rewritten with only the staying tests."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Stay" in src


def test_run_live_mixed_removes_moved_from_source(tmp_path, monkeypatch):
    """Moved tests are removed from the source file."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Move" not in src


def test_run_live_mixed_creates_new_file(tmp_path, monkeypatch):
    """Moved tests are written to a new clause file."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
    )
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_run_live_mixed_keeps_cmake_entry(tmp_path, monkeypatch):
    """Source kept in CMakeLists.txt when source_is_target."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
    )
    cmake = (tmp_path / "CMakeLists.txt").read_text()
    assert "test_non_lrm_aig" in cmake


# ---- main ------------------------------------------------------------------


def test_main(monkeypatch):
    """main calls _run with parsed args."""
    ran = [False]

    def mock_run(_args):
        ran[0] = True

    monkeypatch.setattr(split_tests, "_run", mock_run)
    monkeypatch.setattr(
        split_tests, "_parse_args",
        lambda: SimpleNamespace(
            file="x", output_dir="/tmp", dry_run=True,
            lrm="/lrm.txt", arch="/arch.md",
        ),
    )
    split_tests.main()
    assert ran[0] is True


def test_main_enables_line_buffering(monkeypatch):
    """main reconfigures stdout to line-buffered mode."""
    configured = []

    def mock_reconfigure(**kwargs):
        configured.append(kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(split_tests, "_run", lambda _: None)
    monkeypatch.setattr(
        split_tests, "_parse_args",
        lambda: SimpleNamespace(
            file="x", output_dir="/tmp", dry_run=True,
            lrm="/lrm.txt", arch="/arch.md",
        ),
    )
    split_tests.main()
    assert any(k.get("line_buffering") for k in configured)
