"""Unit tests for main-flow functions in classify_test."""

import sys
from pathlib import Path
from types import ModuleType
from typing import Any

import pytest

M = ModuleType
C = pytest.CaptureFixture[str]
P = pytest.MonkeyPatch


# ---- _parse_args -----------------------------------------------------------


_BASE_ARGV = ["prog", "--file", "f.cpp", "--output-dir", "/out",
              "--lrm", "/lrm.txt", "--suite", "S", "--test", "T",
              "--issue", "1", "--organization", "o", "--repo", "r",
              "--max-lines", "1000"]


def test_parse_args_basic(monkeypatch: P, ct: M) -> None:
    """Parses --file, --output-dir, --lrm, and --test."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    args = _parse_args()
    assert args.file == "f.cpp" and not args.dry_run


def test_parse_args_dry_run(monkeypatch: P, ct: M) -> None:
    """Parses --dry-run flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", [*_BASE_ARGV, "--dry-run"])
    assert _parse_args().dry_run is True


def test_parse_args_lrm(monkeypatch: P, ct: M) -> None:
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


def test_parse_args_test_flag(monkeypatch: P, ct: M) -> None:
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


def test_parse_args_suite_flag(monkeypatch: P, ct: M) -> None:
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


def test_parse_args_suite_required(monkeypatch: P, ct: M) -> None:
    """--suite is required."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--suite"
            and v != "--suite"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_max_lines(monkeypatch: P, ct: M) -> None:
    """Parses --max-lines flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert _parse_args().max_lines == 500


def test_parse_args_max_lines_required(monkeypatch: P, ct: M) -> None:
    """--max-lines is required."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--max-lines"
            and v != "--max-lines"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        _parse_args()

def test_parse_args_issue_optional(monkeypatch: P, ct: M) -> None:
    """--issue is optional and defaults to None."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue"
            and v != "--issue"]
    monkeypatch.setattr(sys, "argv", argv)
    assert _parse_args().issue is None


def test_parse_args_issue_with_value(monkeypatch: P, ct: M) -> None:
    """--issue parses its integer value."""
    _parse_args = getattr(ct, "_parse_args")
    argv = [v if v != "1" or _BASE_ARGV[max(0, i - 1)] != "--issue"
            else "42"
            for i, v in enumerate(_BASE_ARGV)]
    monkeypatch.setattr(sys, "argv", argv)
    assert _parse_args().issue == 42


def test_preamble_name_struct(ct: M) -> None:
    """Extracts struct name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["struct ParseResult {", "  int x;", "};"])
    assert _preamble_name(item) == "ParseResult"


def test_preamble_name_function(ct: M) -> None:
    """Extracts function name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["ParseResult Parse(const std::string& src) {",
                       "  return {};", "}"])
    assert _preamble_name(item) == "Parse"


def test_preamble_name_static_function(ct: M) -> None:
    """Extracts name from static function."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["static bool ParseOk(const std::string& src) {",
                       "  return true;", "}"])
    assert _preamble_name(item) == "ParseOk"


def test_preamble_name_class(ct: M) -> None:
    """Extracts class name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["class Foo {", "};"])
    assert _preamble_name(item) == "Foo"


def test_preamble_name_enum(ct: M) -> None:
    """Extracts enum name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["enum Color {", "  RED,", "};"])
    assert _preamble_name(item) == "Color"


def test_preamble_name_no_match(ct: M) -> None:
    """Returns None for comment-only item."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["// just a comment"])
    assert _preamble_name(item) is None


def test_preamble_name_with_leading_comment(ct: M) -> None:
    """Skips comment lines to find the name."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["// --- Test helpers ---",
                       "struct Foo {", "};"])
    assert _preamble_name(item) == "Foo"


def test_preamble_name_pointer_return(ct: M) -> None:
    """Extracts name from function with pointer return type."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["RtlirDesign* Elaborate(const std::string& src) {",
                       "  return nullptr;", "}"])
    assert _preamble_name(item) == "Elaborate"


def test_preamble_name_static_pointer_return(ct: M) -> None:
    """Extracts name from static function with pointer return type."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=[
        "static ModuleItem* FindItemByKind("
        "const std::vector<ModuleItem*>& items,",
        "  ModuleItemKind kind) {",
        "  return nullptr;", "}"])
    assert _preamble_name(item) == "FindItemByKind"


def test_preamble_name_reference_return(ct: M) -> None:
    """Extracts name from function with reference return type."""
    _preamble_name = getattr(ct, "_preamble_name")
    pi_cls = ct.PreambleItem
    item = pi_cls(lines=["const std::string& GetName() {",
                       '  return name_;', "}"])
    assert _preamble_name(item) == "GetName"


def _test_block(ct: M, body: list[str]) -> Any:
    """Create a TestBlock with specific body lines for preamble tests."""
    return ct.TestBlock(
        suite_name="S", test_name="T",
        lines=["TEST(S, T) {"] + body + ["}"],
        preceding_comments=[],
    )


def test_filter_preamble_keeps_used(ct: M) -> None:
    """Keeps preamble items referenced by test body."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    parse_fn = pi_cls(lines=["Result Parse(const std::string& s) {", "}"])
    elab_fn = pi_cls(lines=["void Elaborate() {", "}"])
    t = _test_block(ct, ["  auto r = Parse(src);"])
    assert parse_fn in _filter_preamble([parse_fn, elab_fn], [t])


def test_filter_preamble_drops_unused(ct: M) -> None:
    """Drops preamble items not referenced by any test."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    parse_fn = pi_cls(lines=["Result Parse(const std::string& s) {", "}"])
    elab_fn = pi_cls(lines=["void Elaborate() {", "}"])
    t = _test_block(ct, ["  auto r = Parse(src);"])
    assert elab_fn not in _filter_preamble([parse_fn, elab_fn], [t])


def _do_transitive_filter(ct: M) -> Any:
    """Filter preamble with transitive deps and return kept list."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    result_struct = pi_cls(lines=["struct ParseResult {", "  int x;", "};"])
    parse_fn = pi_cls(lines=["ParseResult Parse(const std::string& s) {",
                           "  ParseResult r;", "  return r;", "}"])
    t = _test_block(ct, ["  auto r = Parse(src);"])
    return _filter_preamble([result_struct, parse_fn], [t]), result_struct, parse_fn


def test_filter_preamble_transitive_keeps_struct(ct: M) -> None:
    """Transitive dep: keeps ParseResult struct used by Parse."""
    kept, result_struct, _ = _do_transitive_filter(ct)
    assert result_struct in kept


def test_filter_preamble_transitive_keeps_fn(ct: M) -> None:
    """Transitive dep: keeps Parse function used by test."""
    kept, _, parse_fn = _do_transitive_filter(ct)
    assert parse_fn in kept


def test_filter_preamble_keeps_unnamed(ct: M) -> None:
    """Items with no extractable name are always kept."""
    _filter_preamble = getattr(ct, "_filter_preamble")
    pi_cls = ct.PreambleItem
    unnamed = pi_cls(lines=["using Foo = int;"])
    t = _test_block(ct, ["  int x = 1;"])
    assert unnamed in _filter_preamble([unnamed], [t])


def test_group_tests_normal(ct: M, ct_helpers: M) -> None:
    """Groups tests by (prefix, clause)."""
    _group_tests = getattr(ct, "_group_tests")
    _tb = ct_helpers.make_test_block
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    groups = _group_tests([t1, t2])
    assert len(groups[("test_parser_", "6.1")]) == 2


def test_group_tests_defaults(ct: M, ct_helpers: M) -> None:
    """Uses defaults when prefix/clause are None."""
    _group_tests = getattr(ct, "_group_tests")
    _tb = ct_helpers.make_test_block
    t = _tb("A")
    groups = _group_tests([t])
    assert ("test_non_lrm", "non-lrm") in groups


def test_resolve_destinations_create(tmp_path: Path, ct: M, ct_helpers: M) -> None:
    """Creates new files when no merge target exists."""
    _resolve_destinations = getattr(ct, "_resolve_destinations")
    _tb = ct_helpers.make_test_block
    t = _tb("T", prefix="test_parser_", clause="6.1")
    groups = {("test_parser_", "6.1"): [t]}
    to_create, to_merge, _ = _resolve_destinations(
        groups, tmp_path,
    )
    assert len(to_create) == 1 and len(to_merge) == 0


def test_resolve_destinations_merge(tmp_path: Path, ct: M, ct_helpers: M) -> None:
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


def _setup_resolve_dup(ct: M, ct_helpers: M, tmp_path: Path) -> Any:
    """Create a duplicate test scenario for _resolve_destinations tests."""
    resolve = getattr(ct, "_resolve_destinations")
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("TEST(S, T) {\n}\n")
    return resolve, {("test_parser_", "6.1"): [t]}


def test_resolve_destinations_duplicates(tmp_path: Path, ct: M, ct_helpers: M) -> None:
    """Drops duplicate tests."""
    resolve, groups = _setup_resolve_dup(ct, ct_helpers, tmp_path)
    to_create, to_merge, _ = resolve(groups, tmp_path)
    assert len(to_create) == 0 and len(to_merge) == 0


def test_resolve_destinations_all_dupes(tmp_path: Path, capsys: C, ct: M, ct_helpers: M) -> None:
    """Prints removal message with parentheses for each duplicate."""
    resolve, groups = _setup_resolve_dup(ct, ct_helpers, tmp_path)
    resolve(groups, tmp_path)
    assert "- Removed T()" in capsys.readouterr().out


def test_resolve_destinations_dry_run_would_have_removed(tmp_path: Path,
        capsys: C, ct: M, ct_helpers: M) -> None:
    """Dry-run prints 'Would have removed' with parentheses."""
    resolve, groups = _setup_resolve_dup(ct, ct_helpers, tmp_path)
    resolve(groups, tmp_path, dry_run=True)
    assert "- Would have removed T()" in capsys.readouterr().out


def test_resolve_destinations_excludes_source(tmp_path: Path, ct: M, ct_helpers: M) -> None:
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


def test_resolve_destinations_source_is_target(tmp_path: Path, ct: M, ct_helpers: M) -> None:
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


def test_write_files_create(tmp_path: Path, ct: M, ct_helpers: M) -> None:
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


def test_write_files_merge(tmp_path: Path, ct: M, ct_helpers: M) -> None:
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
