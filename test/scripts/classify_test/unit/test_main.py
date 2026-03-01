"""Unit tests for main-flow functions in classify_test."""

import sys
from types import SimpleNamespace

import pytest

import classify_test
from helpers import make_parsed_file as _parsed
from helpers import make_test_block as _tb
from helpers import stub_classifier, stub_side_effects

_parse_args = getattr(classify_test, "_parse_args")
_group_tests = getattr(classify_test, "_group_tests")
_resolve_destinations = getattr(classify_test, "_resolve_destinations")
_write_files = getattr(classify_test, "_write_files")
_run = getattr(classify_test, "_run")


def _make_input_file(tmp_path):
    """Create a minimal test input file and return its path."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
        encoding="utf-8",
    )
    return f


def _parser_response():
    """Return a standard single-test clause response."""
    return {"clause": "6.1", "rationale": "r"}


def _run_args(tmp_path, **overrides):
    """Build a SimpleNamespace with all required _run args."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path), "dry_run": False,
        "lrm": str(tmp_path / "lrm.txt"), "max_lines": None,
        "test": "T", "issue": None, "organization": None,
        "repo": None, "no_commit": False,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


_BASE_ARGV = ["prog", "--file", "f.cpp", "--output-dir", "/out",
              "--lrm", "/lrm.txt", "--test", "T",
              "--issue", "1", "--organization", "o", "--repo", "r"]


def test_parse_args_basic(monkeypatch):
    """Parses --file, --output-dir, --lrm, and --test."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    args = _parse_args()
    assert args.file == "f.cpp" and not args.dry_run


def test_parse_args_dry_run(monkeypatch):
    """Parses --dry-run flag."""
    monkeypatch.setattr(sys, "argv", [*_BASE_ARGV, "--dry-run"])
    assert _parse_args().dry_run is True


def test_parse_args_lrm(monkeypatch):
    """Parses --lrm flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/my/LRM.txt", "--test", "T",
         "--issue", "1", "--organization", "o", "--repo", "r"],
    )
    assert _parse_args().lrm == "/my/LRM.txt"


def test_parse_args_test_flag(monkeypatch):
    """Parses --test flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "Foo",
         "--issue", "1", "--organization", "o", "--repo", "r"],
    )
    assert _parse_args().test == "Foo"


def test_parse_args_max_lines(monkeypatch):
    """Parses --max-lines flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert _parse_args().max_lines == 500


def test_parse_args_max_lines_default(monkeypatch):
    """--max-lines defaults to None."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().max_lines is None


def test_parse_args_no_commit(monkeypatch):
    """Parses --no-commit flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--no-commit"],
    )
    assert _parse_args().no_commit is True


def test_parse_args_no_commit_default(monkeypatch):
    """--no-commit defaults to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().no_commit is False


# ---- _preamble_name / _filter_preamble ------------------------------------

_preamble_name = getattr(classify_test, "_preamble_name")
_filter_preamble = getattr(classify_test, "_filter_preamble")
_PI = classify_test.PreambleItem


def test_preamble_name_struct():
    """Extracts struct name."""
    item = _PI(lines=["struct ParseResult {", "  int x;", "};"])
    assert _preamble_name(item) == "ParseResult"


def test_preamble_name_function():
    """Extracts function name."""
    item = _PI(lines=["ParseResult Parse(const std::string& src) {",
                       "  return {};", "}"])
    assert _preamble_name(item) == "Parse"


def test_preamble_name_static_function():
    """Extracts name from static function."""
    item = _PI(lines=["static bool ParseOk(const std::string& src) {",
                       "  return true;", "}"])
    assert _preamble_name(item) == "ParseOk"


def test_preamble_name_class():
    """Extracts class name."""
    item = _PI(lines=["class Foo {", "};"])
    assert _preamble_name(item) == "Foo"


def test_preamble_name_enum():
    """Extracts enum name."""
    item = _PI(lines=["enum Color {", "  RED,", "};"])
    assert _preamble_name(item) == "Color"


def test_preamble_name_no_match():
    """Returns None for comment-only item."""
    item = _PI(lines=["// just a comment"])
    assert _preamble_name(item) is None


def test_preamble_name_with_leading_comment():
    """Skips comment lines to find the name."""
    item = _PI(lines=["// --- Test helpers ---",
                       "struct Foo {", "};"])
    assert _preamble_name(item) == "Foo"


def test_preamble_name_pointer_return():
    """Extracts name from function with pointer return type."""
    item = _PI(lines=["RtlirDesign* Elaborate(const std::string& src) {",
                       "  return nullptr;", "}"])
    assert _preamble_name(item) == "Elaborate"


def test_preamble_name_static_pointer_return():
    """Extracts name from static function with pointer return type."""
    item = _PI(lines=[
        "static ModuleItem* FindItemByKind("
        "const std::vector<ModuleItem*>& items,",
        "  ModuleItemKind kind) {",
        "  return nullptr;", "}"])
    assert _preamble_name(item) == "FindItemByKind"


def test_preamble_name_reference_return():
    """Extracts name from function with reference return type."""
    item = _PI(lines=["const std::string& GetName() {",
                       '  return name_;', "}"])
    assert _preamble_name(item) == "GetName"


def _test_block(body):
    """Create a TestBlock with specific body lines for preamble tests."""
    return classify_test.TestBlock(
        suite_name="S", test_name="T",
        lines=["TEST(S, T) {"] + body + ["}"],
        preceding_comments=[],
    )


def test_filter_preamble_keeps_used():
    """Keeps preamble items referenced by test body."""
    parse_fn = _PI(lines=["Result Parse(const std::string& s) {", "}"])
    elab_fn = _PI(lines=["void Elaborate() {", "}"])
    t = _test_block(["  auto r = Parse(src);"])
    assert parse_fn in _filter_preamble([parse_fn, elab_fn], [t])


def test_filter_preamble_drops_unused():
    """Drops preamble items not referenced by any test."""
    parse_fn = _PI(lines=["Result Parse(const std::string& s) {", "}"])
    elab_fn = _PI(lines=["void Elaborate() {", "}"])
    t = _test_block(["  auto r = Parse(src);"])
    assert elab_fn not in _filter_preamble([parse_fn, elab_fn], [t])


def _do_transitive_filter():
    """Filter preamble with transitive deps and return kept list."""
    result_struct = _PI(lines=["struct ParseResult {", "  int x;", "};"])
    parse_fn = _PI(lines=["ParseResult Parse(const std::string& s) {",
                           "  ParseResult r;", "  return r;", "}"])
    t = _test_block(["  auto r = Parse(src);"])
    return _filter_preamble([result_struct, parse_fn], [t]), result_struct, parse_fn


def test_filter_preamble_transitive_keeps_struct():
    """Transitive dep: keeps ParseResult struct used by Parse."""
    kept, result_struct, _ = _do_transitive_filter()
    assert result_struct in kept


def test_filter_preamble_transitive_keeps_fn():
    """Transitive dep: keeps Parse function used by test."""
    kept, _, parse_fn = _do_transitive_filter()
    assert parse_fn in kept


def test_filter_preamble_keeps_unnamed():
    """Items with no extractable name are always kept."""
    unnamed = _PI(lines=["using Foo = int;"])
    t = _test_block(["  int x = 1;"])
    assert unnamed in _filter_preamble([unnamed], [t])


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
    to_create, to_merge, _ = _resolve_destinations(
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
    _, to_merge, _ = _resolve_destinations(
        groups, tmp_path,
    )
    assert len(to_merge) == 1


def test_resolve_destinations_duplicates(tmp_path):
    """Drops duplicate tests."""
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    to_create, to_merge, _ = _resolve_destinations(
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
    to_create, to_merge, _ = _resolve_destinations(
        groups, tmp_path, exclude_path=src,
    )
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_source_is_target(tmp_path):
    """Tests already in the correct file are skipped, not recreated."""
    src = tmp_path / "test_non_lrm_vpi.cpp"
    src.write_text("TEST(S, Keep) {\n}\n")
    t = _tb("Keep", prefix="test_non_lrm_", clause="non-lrm:vpi")
    groups = {("test_non_lrm_", "non-lrm:vpi"): [t]}
    to_create, _, _ = _resolve_destinations(
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
        to_create, [], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}},
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
        [], [(f, [t])], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}},
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


def test_run_test_not_found(tmp_path):
    """Exits when --test names a test not in the file."""
    _make_input_file(tmp_path)
    args = _run_args(tmp_path, test="NoSuchTest")
    with pytest.raises(SystemExit):
        _run(args)


def test_run_dry_run_header_shows_test_name(tmp_path, monkeypatch, capsys):
    """Dry-run header shows the test name, not the count."""
    _make_input_file(tmp_path)
    stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "T (dry run)" in capsys.readouterr().out


def test_run_dry_run(tmp_path, monkeypatch, capsys):
    """Dry run classifies but does not write files."""
    _make_input_file(tmp_path)
    stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "dry run" in capsys.readouterr().out


def test_run_dry_run_shows_target(tmp_path, monkeypatch, capsys):
    """Dry-run output shows the target filename."""
    _make_input_file(tmp_path)
    stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "test_parser_clause_06_01.cpp" in capsys.readouterr().out


def _setup_live_run(tmp_path, monkeypatch):
    """Create input file, cmake, and stub classifier for a live run."""
    _make_input_file(tmp_path)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n",
        encoding="utf-8",
    )
    stub_classifier(monkeypatch, _parser_response())
    monkeypatch.setattr(classify_test, "CMAKE_PATH", cmake)
    return _run_args(tmp_path)


def test_run_live_updates_cmake(tmp_path, monkeypatch):
    """Live run updates CMakeLists.txt with new entry."""
    args = _setup_live_run(tmp_path, monkeypatch)
    _run(args)
    assert "test_parser_clause_06_01" in \
        (tmp_path / "CMakeLists.txt").read_text()


def test_run_live_prints_cmake_update(tmp_path, monkeypatch, capsys):
    """Live run prints CMakeLists.txt update message."""
    args = _setup_live_run(tmp_path, monkeypatch)
    _run(args)
    assert "Updated `CMakeLists.txt`" in capsys.readouterr().out


def test_run_live_merge_writes_test(tmp_path, monkeypatch):
    """Live run merging into existing file writes the test."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    args = _setup_live_run(tmp_path, monkeypatch)
    _run(args)
    assert "TEST(S, T)" in \
        (tmp_path / "test_parser_clause_06_01.cpp").read_text()


def test_run_live_merge_prints_merge(tmp_path, monkeypatch, capsys):
    """Live merge prints merge target filename."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    args = _setup_live_run(tmp_path, monkeypatch)
    _run(args)
    assert "Merging into" in capsys.readouterr().out


def _mixed_classifier(prompt, schema=None):
    """Return different classifications based on which test is in prompt."""
    if "Stay" in prompt:
        if schema and "non_lrm_topic" in schema:
            return {"non_lrm_topic": "aig", "rationale": "r"}
        return {"clause": "non-lrm", "rationale": "r"}
    return {"clause": "6.1", "rationale": "r"}


def _run_live_non_lrm(tmp_path, monkeypatch, src_body, classifier,
                      test="T"):
    """Write source, stub externals, and run live pipeline."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(src_body, encoding="utf-8")
    monkeypatch.setattr(
        classify_test, "_call_claude", classifier,
    )
    stub_side_effects(monkeypatch)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        f"# header\nadd_unit_test({src.stem})\n", encoding="utf-8",
    )
    monkeypatch.setattr(classify_test, "CMAKE_PATH", cmake)
    _run(_run_args(tmp_path, file=str(src), test=test))


def _self_named_classifier(_prompt, schema=None):
    """Classify single test as non-lrm with topic aig."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r"}
    return {"clause": "non-lrm", "rationale": "r"}


def test_run_live_self_named(tmp_path, monkeypatch):
    """Source file already in correct location is left untouched."""
    _run_live_non_lrm(
        tmp_path, monkeypatch,
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
        _self_named_classifier,
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


_MIXED_BODY = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Stay) {\n  auto r = Parse(src);\n}\n"
    "TEST(S, Move) {\n  auto r = Parse(src);\n}\n"
)


def test_run_live_mixed_keeps_source(tmp_path, monkeypatch):
    """Source is rewritten with only the staying tests."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
        test="Move",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Stay" in src


def test_run_live_mixed_removes_moved_from_source(tmp_path, monkeypatch):
    """Moved tests are removed from the source file."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
        test="Move",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Move" not in src


def test_run_live_mixed_creates_new_file(tmp_path, monkeypatch):
    """Moved tests are written to a new clause file."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
        test="Move",
    )
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_run_live_mixed_keeps_cmake_entry(tmp_path, monkeypatch):
    """Source kept in CMakeLists.txt when source_is_target."""
    _run_live_non_lrm(
        tmp_path, monkeypatch, _MIXED_BODY, _mixed_classifier,
        test="Move",
    )
    cmake = (tmp_path / "CMakeLists.txt").read_text()
    assert "test_non_lrm_aig" in cmake


def test_run_live_removes_duplicates_from_source(tmp_path, monkeypatch):
    """Live run rewrites source to remove tests that already exist elsewhere."""
    # Source has two tests, both classified as non-lrm:aig
    src_body = (
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, Keep) {\n  auto r = Parse(src);\n}\n"
        "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
    )
    # Pre-create a variant file that already contains Dup
    variant = tmp_path / "test_non_lrm_aig_a.cpp"
    variant.write_text(
        "#include <gtest/gtest.h>\n\nTEST(S, Dup) {\n}\n",
        encoding="utf-8",
    )
    _run_live_non_lrm(
        tmp_path, monkeypatch, src_body, _self_named_classifier,
        test="Dup",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Dup" not in src


def test_run_live_dedup_only_test_rewrites_source(tmp_path, monkeypatch):
    """Source with only the duplicate test is rewritten empty."""
    src_body = (
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
    )
    variant = tmp_path / "test_non_lrm_aig_a.cpp"
    variant.write_text(
        "#include <gtest/gtest.h>\n\nTEST(S, Dup) {\n}\n",
        encoding="utf-8",
    )
    _run_live_non_lrm(
        tmp_path, monkeypatch, src_body, _self_named_classifier,
        test="Dup",
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


def test_run_live_keeps_non_duplicates_when_removing(tmp_path, monkeypatch):
    """Live run keeps non-duplicate tests when removing duplicates."""
    src_body = (
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, Keep) {\n  auto r = Parse(src);\n}\n"
        "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
    )
    variant = tmp_path / "test_non_lrm_aig_a.cpp"
    variant.write_text(
        "#include <gtest/gtest.h>\n\nTEST(S, Dup) {\n}\n",
        encoding="utf-8",
    )
    _run_live_non_lrm(
        tmp_path, monkeypatch, src_body, _self_named_classifier,
        test="Dup",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Keep" in src


# ---- _run with --issue -----------------------------------------------------


def test_run_with_issue_calls_maybe_tick(tmp_path, monkeypatch):
    """_run with --issue calls maybe_tick_issue_checkbox."""
    _make_input_file(tmp_path)
    stub_classifier(monkeypatch, _parser_response())
    called = []
    monkeypatch.setattr(
        classify_test, "maybe_tick_issue_checkbox",
        lambda args, tests: called.append(True),
    )
    args = _run_args(
        tmp_path, dry_run=True,
        issue=42, organization="myorg", repo="myrepo",
    )
    _run(args)
    assert len(called) == 1


def test_run_without_issue_calls_maybe_tick(tmp_path, monkeypatch):
    """_run without --issue still calls maybe_tick_issue_checkbox."""
    _make_input_file(tmp_path)
    stub_classifier(monkeypatch, _parser_response())
    called = []
    monkeypatch.setattr(
        classify_test, "maybe_tick_issue_checkbox",
        lambda args, tests: called.append(True),
    )
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert len(called) == 1


def test_run_no_commit_skips_commit(tmp_path, monkeypatch):
    """_run with no_commit=True does not call commit_classification."""
    args = _setup_live_run(tmp_path, monkeypatch)
    args.no_commit = True
    called = []
    monkeypatch.setattr(
        classify_test, "commit_classification",
        lambda _ctx: called.append(True),
    )
    _run(args)
    assert not called


# ---- main ------------------------------------------------------------------


def test_main(monkeypatch):
    """main calls _run with parsed args."""
    ran = [False]

    def mock_run(_args):
        ran[0] = True

    monkeypatch.setattr(classify_test, "_run", mock_run)
    monkeypatch.setattr(classify_test, "_parse_args", lambda: SimpleNamespace(
        file="x", output_dir="/tmp", dry_run=True, lrm="/lrm.txt",
        issue=None, organization=None, repo=None,
    ))
    classify_test.main()
    assert ran[0] is True


def test_main_enables_line_buffering(monkeypatch):
    """main reconfigures stdout to line-buffered mode."""
    configured = []

    def mock_reconfigure(**kwargs):
        configured.append(kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(classify_test, "_run", lambda _: None)
    monkeypatch.setattr(classify_test, "_parse_args", lambda: SimpleNamespace(
        file="x", output_dir="/tmp", dry_run=True, lrm="/lrm.txt",
        issue=None, organization=None, repo=None,
    ))
    classify_test.main()
    assert any(k.get("line_buffering") for k in configured)
