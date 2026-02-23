"""Integration tests for the split_tests pipeline."""

import subprocess
from types import SimpleNamespace
from unittest.mock import MagicMock

import split_tests

_run = getattr(split_tests, "_run")


# ---- Helpers ---------------------------------------------------------------


def _write_input(tmp_path, body):
    """Write test_input.cpp with standard boilerplate wrapping *body*."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        f"#include <gtest/gtest.h>\n\nnamespace {{\n\n{body}"
        "}  // namespace\n",
        encoding="utf-8",
    )
    return f


def _stub_externals(monkeypatch, tmp_path, response):
    """Stub Claude, LRM/ARCH, CMake, STANDALONE, and git."""
    monkeypatch.setattr(split_tests, "LRM_PATH", tmp_path / "no.txt")
    monkeypatch.setattr(split_tests, "ARCH_PATH", tmp_path / "no.md")
    monkeypatch.setattr(split_tests, "_call_claude", lambda p: response)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n", encoding="utf-8",
    )
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    sa = tmp_path / "STANDALONE.md"
    sa.write_text("- [ ] test_input\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "STANDALONE_PATH", sa)
    monkeypatch.setattr(
        subprocess, "run",
        lambda *_a, **_kw: MagicMock(returncode=0),
    )


def _run_pipeline(tmp_path, dry_run=False):
    """Execute _run on test_input.cpp in *tmp_path*."""
    _run(SimpleNamespace(
        file=str(tmp_path / "test_input.cpp"),
        output_dir=str(tmp_path),
        dry_run=dry_run,
    ))


def _response(*triples):
    """Build Claude response from (test_name, prefix, clause) triples."""
    return {"tests": [
        {"test_name": n, "prefix": p, "clause": c, "rationale": "r"}
        for n, p, c in triples
    ]}


def _do_multi_clause(tmp_path, monkeypatch):
    """Write two tests, classify to different clauses, and run pipeline."""
    _write_input(
        tmp_path,
        "TEST(S, Alpha) {\n  EXPECT_TRUE(true);\n}\n\n"
        "TEST(S, Beta) {\n  EXPECT_EQ(1, 1);\n}\n\n",
    )
    _stub_externals(monkeypatch, tmp_path, _response(
        ("Alpha", "test_parser_", "6.1"),
        ("Beta", "test_lexer_", "5.3"),
    ))
    _run_pipeline(tmp_path)
    return tmp_path


def _do_merge(tmp_path, monkeypatch):
    """Merge a new test into an existing clause file, return its path."""
    existing = tmp_path / "test_parser_clause_06_01.cpp"
    existing.write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    _write_input(tmp_path, "TEST(S, Fresh) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _response(
        ("Fresh", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path)
    return existing


def _do_dry_run(tmp_path, monkeypatch):
    """Run pipeline in dry-run mode, return tmp_path."""
    _write_input(tmp_path, "TEST(S, DryT) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _response(
        ("DryT", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, dry_run=True)
    return tmp_path


# ---- Multi-clause split ----------------------------------------------------


def test_multi_clause_creates_parser_file(tmp_path, monkeypatch):
    """Parser clause file is created for the parser-classified test."""
    assert (_do_multi_clause(tmp_path, monkeypatch)
            / "test_parser_clause_06_01.cpp").exists()


def test_multi_clause_creates_lexer_file(tmp_path, monkeypatch):
    """Lexer clause file is created for the lexer-classified test."""
    assert (_do_multi_clause(tmp_path, monkeypatch)
            / "test_lexer_clause_05_03.cpp").exists()


def test_multi_clause_parser_contains_alpha(tmp_path, monkeypatch):
    """Parser file contains the Alpha test."""
    assert "TEST(S, Alpha)" in (
        _do_multi_clause(tmp_path, monkeypatch)
        / "test_parser_clause_06_01.cpp"
    ).read_text()


def test_multi_clause_lexer_contains_beta(tmp_path, monkeypatch):
    """Lexer file contains the Beta test."""
    assert "TEST(S, Beta)" in (
        _do_multi_clause(tmp_path, monkeypatch)
        / "test_lexer_clause_05_03.cpp"
    ).read_text()


def test_multi_clause_deletes_input(tmp_path, monkeypatch):
    """Input file is removed after splitting."""
    assert not (_do_multi_clause(tmp_path, monkeypatch)
                / "test_input.cpp").exists()


def test_multi_clause_cmake_has_new_entry(tmp_path, monkeypatch):
    """CMakeLists.txt contains the new parser clause entry."""
    assert "test_parser_clause_06_01" in (
        _do_multi_clause(tmp_path, monkeypatch) / "CMakeLists.txt"
    ).read_text()


def test_multi_clause_cmake_drops_old_entry(tmp_path, monkeypatch):
    """CMakeLists.txt no longer contains the old test_input entry."""
    assert "test_input" not in (
        _do_multi_clause(tmp_path, monkeypatch) / "CMakeLists.txt"
    ).read_text()


def test_multi_clause_standalone_cleaned(tmp_path, monkeypatch):
    """STANDALONE.md no longer references test_input."""
    assert "test_input" not in (
        _do_multi_clause(tmp_path, monkeypatch) / "STANDALONE.md"
    ).read_text()


# ---- Merge into existing file ----------------------------------------------


def test_merge_adds_new_test(tmp_path, monkeypatch):
    """Merged file contains the new test."""
    assert "TEST(S, Fresh)" in _do_merge(tmp_path, monkeypatch).read_text()


def test_merge_preserves_old_test(tmp_path, monkeypatch):
    """Merged file still contains the pre-existing test."""
    assert "TEST(S, Old)" in _do_merge(tmp_path, monkeypatch).read_text()


# ---- Deduplication ---------------------------------------------------------


def test_dedup_reports_duplicate(tmp_path, monkeypatch, capsys):
    """Tests already in the target file are reported as duplicates."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "TEST(S, Dup) {\n}\n", encoding="utf-8",
    )
    _write_input(tmp_path, "TEST(S, Dup) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _response(
        ("Dup", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path)
    assert "DUPLICATE" in capsys.readouterr().out


# ---- Non-LRM topic routing ------------------------------------------------


def test_non_lrm_topic_creates_named_file(tmp_path, monkeypatch):
    """Non-LRM test with topic creates test_non_lrm_<topic>.cpp."""
    _write_input(tmp_path, "TEST(S, InternalHelper) {\n}\n\n")
    resp = {"tests": [
        {"test_name": "InternalHelper", "prefix": "test_non_lrm_",
         "clause": "non-lrm", "non_lrm_topic": "aig", "rationale": "r"},
    ]}
    _stub_externals(monkeypatch, tmp_path, resp)
    _run_pipeline(tmp_path)
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


# ---- Annex routing ---------------------------------------------------------


def test_annex_creates_annex_file(tmp_path, monkeypatch):
    """Annex-clause test creates test_<prefix>_annex_<letter>_<padded>.cpp."""
    _write_input(tmp_path, "TEST(S, GrammarRule) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _response(
        ("GrammarRule", "test_parser_", "A.6.3"),
    ))
    _run_pipeline(tmp_path)
    assert (tmp_path / "test_parser_annex_a_06_03.cpp").exists()


# ---- Dry run ---------------------------------------------------------------


def test_dry_run_no_output_files(tmp_path, monkeypatch):
    """Dry run does not create any output files."""
    assert not (_do_dry_run(tmp_path, monkeypatch)
                / "test_parser_clause_06_01.cpp").exists()


def test_dry_run_preserves_input(tmp_path, monkeypatch):
    """Dry run does not delete the input file."""
    assert (_do_dry_run(tmp_path, monkeypatch)
            / "test_input.cpp").exists()


# ---- Preamble propagation --------------------------------------------------


def test_preamble_propagated_to_output(tmp_path, monkeypatch):
    """Global preamble from input appears in generated output files."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\n"
        "struct Fixture {\n  int x;\n};\n\n"
        "namespace {\n\nTEST(S, T) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    _stub_externals(monkeypatch, tmp_path, _response(
        ("T", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path)
    assert "struct Fixture {" in (
        tmp_path / "test_parser_clause_06_01.cpp"
    ).read_text()


# ---- LRM quote stripping ---------------------------------------------------


def test_lrm_quotes_stripped_in_output(tmp_path, monkeypatch):
    """LRM prose quotes in comments are stripped from generated output."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\nnamespace {\n\n"
        "// \u00a76.1: \"A module declaration...\"\n"
        "TEST(S, QuotedTest) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    _stub_externals(monkeypatch, tmp_path, _response(
        ("QuotedTest", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path)
    assert "A module declaration" not in (
        tmp_path / "test_parser_clause_06_01.cpp"
    ).read_text()


# ---- Roundtrip parse -------------------------------------------------------


def test_output_reparseable(tmp_path, monkeypatch):
    """Generated output can be re-parsed by parse_file without errors."""
    _write_input(tmp_path, "TEST(S, Round) {\n  int x = 1;\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _response(
        ("Round", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path)
    assert len(split_tests.parse_file(
        tmp_path / "test_parser_clause_06_01.cpp",
    ).all_tests) == 1
