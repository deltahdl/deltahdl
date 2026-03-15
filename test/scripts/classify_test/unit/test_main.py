"""Unit tests for main-flow functions in classify_test."""

import sys
from types import SimpleNamespace

import pytest


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
    return {"clause": "6.1", "rationale": "r",
            "suite_name": "Parsing", "test_name": "T"}


def _run_args(tmp_path, **overrides):
    """Build a SimpleNamespace with all required _run args."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path), "dry_run": False,
        "lrm": str(tmp_path / "lrm.txt"), "max_lines": 1000,
        "suite": "S", "test": "T", "issue": None, "organization": None,
        "repo": None, "no_commit": False, "continue_session": False,
        "against": "",
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


_BASE_ARGV = ["prog", "--file", "f.cpp", "--output-dir", "/out",
              "--lrm", "/lrm.txt", "--suite", "S", "--test", "T",
              "--issue", "1", "--organization", "o", "--repo", "r",
              "--max-lines", "1000"]


def test_parse_args_basic(monkeypatch, ct):
    """Parses --file, --output-dir, --lrm, and --test."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    args = _parse_args()
    assert args.file == "f.cpp" and not args.dry_run


def test_parse_args_dry_run(monkeypatch, ct):
    """Parses --dry-run flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", [*_BASE_ARGV, "--dry-run"])
    assert _parse_args().dry_run is True


def test_parse_args_lrm(monkeypatch, ct):
    """Parses --lrm flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/my/LRM.txt", "--suite", "S", "--test", "T",
         "--issue", "1", "--organization", "o", "--repo", "r",
         "--max-lines", "1000"],
    )
    assert _parse_args().lrm == "/my/LRM.txt"


def test_parse_args_test_flag(monkeypatch, ct):
    """Parses --test flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--suite", "S", "--test", "Foo",
         "--issue", "1", "--organization", "o", "--repo", "r",
         "--max-lines", "1000"],
    )
    assert _parse_args().test == "Foo"


def test_parse_args_suite_flag(monkeypatch, ct):
    """Parses --suite flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--suite", "MySuite", "--test", "Foo",
         "--issue", "1", "--organization", "o", "--repo", "r",
         "--max-lines", "1000"],
    )
    assert _parse_args().suite == "MySuite"


def test_parse_args_suite_required(monkeypatch, ct):
    """--suite is required."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--suite"
            and v != "--suite"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_max_lines(monkeypatch, ct):
    """Parses --max-lines flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert _parse_args().max_lines == 500


def test_parse_args_max_lines_required(monkeypatch, ct):
    """--max-lines is required."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--max-lines"
            and v != "--max-lines"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()

def test_parse_args_issue_optional(monkeypatch, ct):
    """--issue is optional and defaults to None."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue"
            and v != "--issue"]
    monkeypatch.setattr(sys, "argv", argv)
    assert _parse_args().issue is None


def test_parse_args_issue_with_value(monkeypatch, ct):
    """--issue parses its integer value."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v if v != "1" or _BASE_ARGV[max(0, i - 1)] != "--issue"
            else "42"
            for i, v in enumerate(_BASE_ARGV)]
    monkeypatch.setattr(sys, "argv", argv)
    assert _parse_args().issue == 42



def test_preamble_name_struct(ct):
    """Extracts struct name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["struct ParseResult {", "  int x;", "};"])
    assert _preamble_name(item) == "ParseResult"


def test_preamble_name_function(ct):
    """Extracts function name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["ParseResult Parse(const std::string& src) {",
                       "  return {};", "}"])
    assert _preamble_name(item) == "Parse"


def test_preamble_name_static_function(ct):
    """Extracts name from static function."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["static bool ParseOk(const std::string& src) {",
                       "  return true;", "}"])
    assert _preamble_name(item) == "ParseOk"


def test_preamble_name_class(ct):
    """Extracts class name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["class Foo {", "};"])
    assert _preamble_name(item) == "Foo"


def test_preamble_name_enum(ct):
    """Extracts enum name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["enum Color {", "  RED,", "};"])
    assert _preamble_name(item) == "Color"


def test_preamble_name_no_match(ct):
    """Returns None for comment-only item."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["// just a comment"])
    assert _preamble_name(item) is None


def test_preamble_name_with_leading_comment(ct):
    """Skips comment lines to find the name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["// --- Test helpers ---",
                       "struct Foo {", "};"])
    assert _preamble_name(item) == "Foo"


def test_preamble_name_pointer_return(ct):
    """Extracts name from function with pointer return type."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["RtlirDesign* Elaborate(const std::string& src) {",
                       "  return nullptr;", "}"])
    assert _preamble_name(item) == "Elaborate"


def test_preamble_name_static_pointer_return(ct):
    """Extracts name from static function with pointer return type."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=[
        "static ModuleItem* FindItemByKind("
        "const std::vector<ModuleItem*>& items,",
        "  ModuleItemKind kind) {",
        "  return nullptr;", "}"])
    assert _preamble_name(item) == "FindItemByKind"


def test_preamble_name_reference_return(ct):
    """Extracts name from function with reference return type."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["const std::string& GetName() {",
                       '  return name_;', "}"])
    assert _preamble_name(item) == "GetName"


def _test_block(ct, body):
    """Create a TestBlock with specific body lines for preamble tests."""
    return ct.TestBlock(
        suite_name="S", test_name="T",
        lines=["TEST(S, T) {"] + body + ["}"],
        preceding_comments=[],
    )


def test_filter_preamble_keeps_used(ct):
    """Keeps preamble items referenced by test body."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    parse_fn = pi_cls(lines=["Result Parse(const std::string& s) {", "}"])
    elab_fn = pi_cls(lines=["void Elaborate() {", "}"])
    t = _test_block(ct, ["  auto r = Parse(src);"])
    assert parse_fn in _filter_preamble([parse_fn, elab_fn], [t])


def test_filter_preamble_drops_unused(ct):
    """Drops preamble items not referenced by any test."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    parse_fn = pi_cls(lines=["Result Parse(const std::string& s) {", "}"])
    elab_fn = pi_cls(lines=["void Elaborate() {", "}"])
    t = _test_block(ct, ["  auto r = Parse(src);"])
    assert elab_fn not in _filter_preamble([parse_fn, elab_fn], [t])


def _do_transitive_filter(ct):
    """Filter preamble with transitive deps and return kept list."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    result_struct = pi_cls(lines=["struct ParseResult {", "  int x;", "};"])
    parse_fn = pi_cls(lines=["ParseResult Parse(const std::string& s) {",
                           "  ParseResult r;", "  return r;", "}"])
    t = _test_block(ct, ["  auto r = Parse(src);"])
    return _filter_preamble([result_struct, parse_fn], [t]), result_struct, parse_fn


def test_filter_preamble_transitive_keeps_struct(ct):
    """Transitive dep: keeps ParseResult struct used by Parse."""
    kept, result_struct, _ = _do_transitive_filter(ct)
    assert result_struct in kept


def test_filter_preamble_transitive_keeps_fn(ct):
    """Transitive dep: keeps Parse function used by test."""
    kept, _, parse_fn = _do_transitive_filter(ct)
    assert parse_fn in kept


def test_filter_preamble_keeps_unnamed(ct):
    """Items with no extractable name are always kept."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    unnamed = pi_cls(lines=["using Foo = int;"])
    t = _test_block(ct, ["  int x = 1;"])
    assert unnamed in _filter_preamble([unnamed], [t])



def test_group_tests_normal(ct, ct_helpers):
    """Groups tests by (prefix, clause)."""
    _group_tests = getattr(ct, "_group_tests")
    _tb = ct_helpers.make_test_block
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    groups = _group_tests([t1, t2])
    assert len(groups[("test_parser_", "6.1")]) == 2


def test_group_tests_defaults(ct, ct_helpers):
    """Uses defaults when prefix/clause are None."""
    _group_tests = getattr(ct, "_group_tests")
    _tb = ct_helpers.make_test_block
    t = _tb("A")
    groups = _group_tests([t])
    assert ("test_non_lrm", "non-lrm") in groups



def test_resolve_destinations_create(tmp_path, ct, ct_helpers):
    """Creates new files when no merge target exists."""
    _resolve_destinations = getattr(ct, "_resolve_destinations")
    _tb = ct_helpers.make_test_block
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    to_create, to_merge, _ = _resolve_destinations(
        groups, tmp_path,
    )
    assert len(to_create) == 1 and len(to_merge) == 0


def test_resolve_destinations_merge(tmp_path, ct, ct_helpers):
    """Merges into existing file."""
    _resolve_destinations = getattr(ct, "_resolve_destinations")
    _tb = ct_helpers.make_test_block
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "TEST(S, Old) {}\n",
    )
    t = _tb("New", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    _, to_merge, _ = _resolve_destinations(
        groups, tmp_path,
    )
    assert len(to_merge) == 1


def _setup_resolve_dup(ct, ct_helpers, tmp_path):
    """Create a duplicate test scenario for _resolve_destinations tests."""
    resolve = getattr(ct, "_resolve_destinations")
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    return resolve, {("test_parser_", "6.1"): [t]}


def test_resolve_destinations_duplicates(tmp_path, ct, ct_helpers):
    """Drops duplicate tests."""
    resolve, groups = _setup_resolve_dup(ct, ct_helpers, tmp_path)
    to_create, to_merge, _ = resolve(groups, tmp_path)
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_all_dupes(tmp_path, capsys, ct, ct_helpers):
    """Prints removal message with parentheses for each duplicate."""
    resolve, groups = _setup_resolve_dup(ct, ct_helpers, tmp_path)
    resolve(groups, tmp_path)
    assert "- Removed T()" in capsys.readouterr().out


def test_resolve_destinations_dry_run_would_have_removed(
    tmp_path, capsys, ct, ct_helpers,
):
    """Dry-run prints 'Would have removed' with parentheses."""
    resolve, groups = _setup_resolve_dup(ct, ct_helpers, tmp_path)
    resolve(groups, tmp_path, dry_run=True)
    assert "- Would have removed T()" in capsys.readouterr().out


def test_resolve_destinations_excludes_source(tmp_path, ct, ct_helpers):
    """Source file matching target is skipped (already correct)."""
    _resolve_destinations = getattr(ct, "_resolve_destinations")
    _tb = ct_helpers.make_test_block
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text("TEST(S, Self) {\n}\n")
    t = _tb("Self", prefix="test_non_lrm_", clause="non-lrm:aig")
    groups = {("test_non_lrm_", "non-lrm:aig"): [t]}
    to_create, to_merge, _ = _resolve_destinations(
        groups, tmp_path, exclude_path=src,
    )
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_source_is_target(tmp_path, ct, ct_helpers):
    """Tests already in the correct file are skipped, not recreated."""
    _resolve_destinations = getattr(ct, "_resolve_destinations")
    _tb = ct_helpers.make_test_block
    src = tmp_path / "test_non_lrm_vpi.cpp"
    src.write_text("TEST(S, Keep) {\n}\n")
    t = _tb("Keep", prefix="test_non_lrm_", clause="non-lrm:vpi")
    groups = {("test_non_lrm_", "non-lrm:vpi"): [t]}
    to_create, _, _ = _resolve_destinations(
        groups, tmp_path, exclude_path=src,
    )
    assert len(to_create) == 0



def test_write_files_create(tmp_path, ct, ct_helpers):
    """Creates new files on disk."""
    _write_files = getattr(ct, "_write_files")
    _tb = ct_helpers.make_test_block
    _parsed = ct_helpers.make_parsed_file
    t = _tb("T", comments=[])
    parsed = _parsed()
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    names = _write_files(
        to_create, [], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}},
    )
    assert "test_parser_clause_06_01" in names


def test_write_files_merge(tmp_path, ct, ct_helpers):
    """Merges tests into existing files."""
    _write_files = getattr(ct, "_write_files")
    _tb = ct_helpers.make_test_block
    _parsed = ct_helpers.make_parsed_file
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


def test_run_file_not_found(tmp_path, ct):
    """Exits when input file does not exist."""
    _run = getattr(ct, "_run")
    args = _run_args(tmp_path, file=str(tmp_path / "missing.cpp"))
    with pytest.raises(SystemExit):
        _run(args)


def test_run_no_test_blocks(tmp_path, ct):
    """Exits when file has no TEST blocks."""
    _run = getattr(ct, "_run")
    f = tmp_path / "empty.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\nint x = 0;\n",
        encoding="utf-8",
    )
    args = _run_args(tmp_path, file=str(f))
    with pytest.raises(SystemExit):
        _run(args)


def test_run_test_not_found(tmp_path, ct):
    """Exits when --test names a test not in the file."""
    _run = getattr(ct, "_run")
    _make_input_file(tmp_path)
    args = _run_args(tmp_path, test="NoSuchTest")
    with pytest.raises(SystemExit):
        _run(args)


def test_run_dry_run_shows_target(tmp_path, monkeypatch, capsys, ct,
                                  ct_helpers):
    """Dry-run output shows the target filename."""
    _run = getattr(ct, "_run")
    _make_input_file(tmp_path)
    ct_helpers.stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "test_parser_clause_06_01.cpp" in capsys.readouterr().out


def test_run_prints_action_moved(tmp_path, monkeypatch, capsys, ct,
                                 ct_helpers):
    """_run prints action line when test is moved."""
    _run = getattr(ct, "_run")
    _make_input_file(tmp_path)
    ct_helpers.stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "Action: Moved to test_parser_clause_06_01.cpp" in capsys.readouterr().out


def _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch):
    """Create input file, cmake, and stub classifier for a live run."""
    _make_input_file(tmp_path)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n",
        encoding="utf-8",
    )
    ct_helpers.stub_classifier(monkeypatch, _parser_response())
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    return _run_args(tmp_path)


def test_run_live_updates_cmake(tmp_path, monkeypatch, ct, ct_helpers):
    """Live run updates CMakeLists.txt with new entry."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "test_parser_clause_06_01" in \
        (tmp_path / "CMakeLists.txt").read_text()


def test_run_live_prints_cmake_update(tmp_path, monkeypatch, capsys, ct,
                                      ct_helpers):
    """Live run prints CMakeLists.txt update message."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "Updated `CMakeLists.txt`" in capsys.readouterr().out


def test_run_live_prints_cmake_updating(tmp_path, monkeypatch, capsys, ct,
                                        ct_helpers):
    """Live run prints 'Updating' with rationale before the update."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    out = capsys.readouterr().out
    assert "Updating `CMakeLists.txt` because" in out


def test_run_live_delete_prints_message(tmp_path, monkeypatch, capsys, ct,
                                        ct_helpers):
    """Live run prints delete message when source file is removed."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    out = capsys.readouterr().out
    assert "Deleting test_input.cpp because all its tests" \
           " were moved elsewhere" in out


def test_run_live_merge_writes_test(tmp_path, monkeypatch, ct, ct_helpers):
    """Live run merging into existing file writes the test."""
    _run = getattr(ct, "_run")
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "TEST(Parsing, T)" in \
        (tmp_path / "test_parser_clause_06_01.cpp").read_text()


def _setup_live_merge(ct, ct_helpers, tmp_path, monkeypatch):
    """Create existing clause file and set up a live merge run."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    return _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)


def test_run_live_merge_prints_test_name(tmp_path, monkeypatch, capsys, ct,
                                         ct_helpers):
    """Live merge message includes the test name."""
    _run = getattr(ct, "_run")
    args = _setup_live_merge(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "Merging test T into" in capsys.readouterr().out


def test_run_live_merge_prints_rationale(tmp_path, monkeypatch, capsys, ct,
                                         ct_helpers):
    """Live merge message includes a rationale."""
    _run = getattr(ct, "_run")
    args = _setup_live_merge(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "because" in capsys.readouterr().out


def _mixed_classifier(prompt, schema=None, **_kw):
    """Return different classifications based on which test is in prompt."""
    if "Stay" in prompt:
        if schema and "non_lrm_topic" in schema:
            return {"non_lrm_topic": "aig", "rationale": "r",
                    "suite_name": "AigGraph", "test_name": "Stay"}
        return {"clause": "non-lrm", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "Stay"}
    return {"clause": "6.1", "rationale": "r",
            "suite_name": "Parsing", "test_name": "Move"}


def _run_live_non_lrm(ct, tmp_path, monkeypatch, *, src_body, test="T"):
    """Write source and run live pipeline.

    Callers must stub _call_claude and side effects before calling.
    """
    _run = getattr(ct, "_run")
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(src_body, encoding="utf-8")
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        f"# header\nadd_unit_test({src.stem})\n", encoding="utf-8",
    )
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    _run(_run_args(tmp_path, file=str(src), test=test))


def _self_named_classifier(_prompt, schema=None, **_kw):
    """Classify single test as non-lrm with topic aig."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "T"}
    return {"clause": "non-lrm", "rationale": "r",
            "suite_name": "AigGraph", "test_name": "T"}


def test_run_prints_action_kept(tmp_path, monkeypatch, capsys, ct, ct_helpers):
    """_run prints action line when test is kept in the same file."""
    monkeypatch.setattr(ct, "_call_claude", _self_named_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body="#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
    )
    assert "Action: Kept in the same file but renamed suite to AigGraph" in capsys.readouterr().out


def test_run_live_self_named(tmp_path, monkeypatch, ct, ct_helpers):
    """Source file already in correct location is left untouched."""
    monkeypatch.setattr(ct, "_call_claude", _self_named_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body="#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


def _no_rename_classifier(_prompt, schema=None, **_kw):
    """Classify single test as non-lrm/aig without renaming."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "S", "test_name": "T"}
    return {"clause": "non-lrm", "rationale": "r",
            "suite_name": "S", "test_name": "T"}


def test_run_live_self_named_no_rename(tmp_path, monkeypatch, ct, ct_helpers):
    """Source-is-target with no rename leaves file intact."""
    monkeypatch.setattr(ct, "_call_claude", _no_rename_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body="#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


_MIXED_BODY = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Stay) {\n  auto r = Parse(src);\n}\n"
    "TEST(S, Move) {\n  auto r = Parse(src);\n}\n"
)


def test_run_live_mixed_keeps_source(tmp_path, monkeypatch, ct, ct_helpers):
    """Source is rewritten with only the staying tests."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Stay" in src


def test_run_live_mixed_removes_moved_from_source(tmp_path, monkeypatch, ct,
                                                   ct_helpers):
    """Moved tests are removed from the source file."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Move" not in src


def test_run_live_mixed_creates_new_file(tmp_path, monkeypatch, ct,
                                         ct_helpers):
    """Moved tests are written to a new clause file."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_run_live_mixed_keeps_cmake_entry(tmp_path, monkeypatch, ct,
                                          ct_helpers):
    """Source kept in CMakeLists.txt when source_is_target."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    cmake = (tmp_path / "CMakeLists.txt").read_text()
    assert "test_non_lrm_aig" in cmake


_DUP_BODY_TWO = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Keep) {\n  auto r = Parse(src);\n}\n"
    "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
)

_DUP_BODY_ONE = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
)


def _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, src_body):
    """Pre-create variant with Dup, stub externals, and run live pipeline."""
    variant = tmp_path / "test_non_lrm_aig_a.cpp"
    variant.write_text(
        "#include <gtest/gtest.h>\n\nTEST(S, Dup) {\n  auto r = Parse(src);\n}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(ct, "_call_claude", _self_named_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(ct, tmp_path, monkeypatch, src_body=src_body, test="Dup")


def test_run_live_removes_duplicates_from_source(tmp_path, monkeypatch, ct,
                                                  ct_helpers):
    """Live run rewrites source to remove tests that already exist elsewhere."""
    _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, _DUP_BODY_TWO)
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Dup" not in src


def test_run_live_dedup_only_test_rewrites_source(tmp_path, monkeypatch, ct,
                                                   ct_helpers):
    """Source with only the duplicate test is rewritten empty."""
    _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, _DUP_BODY_ONE)
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


def test_run_live_keeps_non_duplicates_when_removing(tmp_path, monkeypatch,
                                                      ct, ct_helpers):
    """Live run keeps non-duplicate tests when removing duplicates."""
    _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, _DUP_BODY_TWO)
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Keep" in src



def _rewrite_source_fixture(ct, ct_helpers, tmp_path):
    """Create parsed file, groups, and temp file for rewrite tests."""
    t = ct_helpers.make_test_block(
        "T", prefix="test_parser_", clause="6.1",
    )
    parsed = ct.ParsedFile(
        includes=["#include <gtest/gtest.h>"],
        using_line=None, has_namespace_wrapper=True,
        global_preamble=[], section_preamble=[],
        all_tests=[t],
    )
    groups = {("test_parser_", "6.1"): [t]}
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("old", encoding="utf-8")
    return parsed, groups, f


def test_rewrite_source_writes_file(tmp_path, ct, ct_helpers):
    """_rewrite_source writes the file with staying tests."""
    parsed, groups, f = _rewrite_source_fixture(ct, ct_helpers, tmp_path)
    getattr(ct, "_rewrite_source")(
        f, groups, parsed, {}, "test_parser_clause_06_01",
    )
    assert "TEST" in f.read_text()


def test_update_source_calls_rewrite(tmp_path, ct, ct_helpers):
    """_update_source delegates to _rewrite_source when source_is_target."""
    parsed, groups, f = _rewrite_source_fixture(ct, ct_helpers, tmp_path)
    result = getattr(ct, "_update_source")(f, parsed, {
        "suite": "S", "test": "T", "groups": groups,
        "titles": {}, "stem": "test_parser_clause_06_01",
        "source_is_target": True,
    })
    assert result == 1


# ---- _run with --issue -----------------------------------------------------


def _setup_maybe_update_test(ct, ct_helpers, tmp_path, monkeypatch):
    """Set up a live run and capture maybe_update_issue_status calls."""
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    monkeypatch.setattr(ct, "commit_classification", lambda _ctx: "abc123")
    called = []
    gh = __import__("classify_test._github", fromlist=["_github"])
    monkeypatch.setattr(
        gh, "maybe_update_issue_status",
        lambda *_a, **_kw: called.append(True),
    )
    return getattr(ct, "_run"), called, args


def test_run_with_issue_calls_maybe_tick(tmp_path, monkeypatch, ct,
                                         ct_helpers):
    """_run with --issue calls maybe_update_issue_status."""
    _run, called, args = _setup_maybe_update_test(
        ct, ct_helpers, tmp_path, monkeypatch,
    )
    args.issue = 42
    args.organization = "myorg"
    args.repo = "myrepo"
    _run(args)
    assert len(called) == 1


def test_run_without_issue_skips_maybe_tick(tmp_path, monkeypatch, ct,
                                            ct_helpers):
    """_run without --issue skips maybe_update_issue_status."""
    _run, called, args = _setup_maybe_update_test(
        ct, ct_helpers, tmp_path, monkeypatch,
    )
    _run(args)
    assert len(called) == 0


def test_run_dry_run_skips_issue_update(tmp_path, monkeypatch, ct,
                                        ct_helpers):
    """_run with --dry-run does not update the issue."""
    _run, called, args = _setup_maybe_update_test(
        ct, ct_helpers, tmp_path, monkeypatch,
    )
    args.dry_run = True
    args.issue = 42
    args.organization = "myorg"
    args.repo = "myrepo"
    _run(args)
    assert len(called) == 0


def test_run_no_commit_skips_commit(tmp_path, monkeypatch, ct, ct_helpers):
    """_run with no_commit=True does not call commit_classification."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    args.no_commit = True
    called = []
    monkeypatch.setattr(
        ct, "commit_classification",
        lambda _ctx: called.append(True),
    )
    _run(args)
    assert not called


# ---- rename in place -------------------------------------------------------


def _rename_classifier(_prompt, schema=None, **_kw):
    """Classify single test as non-lrm:aig and rename to Renamed."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "Renamed"}
    return {"clause": "non-lrm", "rationale": "r",
            "suite_name": "AigGraph", "test_name": "Renamed"}

_RENAME_BODY = ("#include <gtest/gtest.h>\n\n"
                "TEST(S, T) {\n  auto r = Parse(src);\n}\n")


def _run_rename(ct, ct_helpers, tmp_path, monkeypatch):
    """Run live non-lrm pipeline with the rename classifier."""
    monkeypatch.setattr(ct, "_call_claude", _rename_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(ct, tmp_path, monkeypatch, src_body=_RENAME_BODY)


def test_run_rename_in_place_rewrites_file(tmp_path, monkeypatch, ct,
                                            ct_helpers):
    """Rename-in-place rewrites the source file with the new test name."""
    _run_rename(ct, ct_helpers, tmp_path, monkeypatch)
    assert "TEST(AigGraph, Renamed)" in \
        (tmp_path / "test_non_lrm_aig.cpp").read_text()


def test_run_rename_in_place_removes_old_name(tmp_path, monkeypatch, ct,
                                               ct_helpers):
    """Rename-in-place removes the old TEST macro name from the file."""
    _run_rename(ct, ct_helpers, tmp_path, monkeypatch)
    assert "TEST(S, T)" not in \
        (tmp_path / "test_non_lrm_aig.cpp").read_text()


def _run_rename_commit(ct, tmp_path, monkeypatch):
    """Capture commits from the rename pipeline."""
    monkeypatch.setattr(ct, "_call_claude", _rename_classifier)
    committed = []
    monkeypatch.setattr(ct, "commit_classification", committed.append)
    _run_live_non_lrm(ct, tmp_path, monkeypatch, src_body=_RENAME_BODY)
    return committed


def test_run_rename_in_place_commits(tmp_path, monkeypatch, ct):
    """Rename-in-place calls commit_classification."""
    assert len(_run_rename_commit(ct, tmp_path, monkeypatch)) == 1


def test_run_commit_includes_action(tmp_path, monkeypatch, ct):
    """Commit message includes the action remark."""
    committed = _run_rename_commit(ct, tmp_path, monkeypatch)
    assert "action" in committed[0]


def test_run_rename_in_place_no_commit(tmp_path, monkeypatch, ct):
    """Rename-in-place with no_commit=True skips commit_classification."""
    monkeypatch.setattr(ct, "_call_claude", _rename_classifier)
    committed = []
    monkeypatch.setattr(ct, "commit_classification", committed.append)
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(_RENAME_BODY, encoding="utf-8")
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(f"# header\nadd_unit_test({src.stem})\n",
                     encoding="utf-8")
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    args = _run_args(tmp_path, file=str(src), no_commit=True)
    getattr(ct, "_run")(args)
    assert not committed


def test_run_against_none_skips(tmp_path, monkeypatch, ct, ct_helpers):
    """_run returns early when classify_test_block returns None."""
    _make_input_file(tmp_path)
    ct_helpers.stub_classifier(monkeypatch, {
        "clause": "none", "rationale": "r",
        "suite_name": "S", "test_name": "T",
    })
    args = _run_args(tmp_path, against="23.2.1")
    getattr(ct, "_run")(args)
    assert (tmp_path / "test_input.cpp").exists()


def _stub_main(monkeypatch, ct, run_fn):
    """Stub _parse_args and _run for main() tests."""
    monkeypatch.setattr(ct, "_run", run_fn)
    monkeypatch.setattr(ct, "_parse_args", lambda: SimpleNamespace(
        file="x", output_dir="/tmp", dry_run=True, lrm="/lrm.txt",
        issue=None, organization=None, repo=None,
    ))


def test_main(monkeypatch, ct):
    """main calls _run with parsed args."""
    ran = [False]
    _stub_main(monkeypatch, ct, lambda _: ran.__setitem__(0, True))
    ct.main()
    assert ran[0] is True


def test_main_enables_line_buffering(monkeypatch, ct):
    """main reconfigures stdout to line-buffered mode."""
    configured = []
    monkeypatch.setattr(
        sys.stdout, "reconfigure",
        lambda **kw: configured.append(kw),
    )
    _stub_main(monkeypatch, ct, lambda _: None)
    ct.main()
    assert any(k.get("line_buffering") for k in configured)
