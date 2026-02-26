"""Integration tests for the classify_tests_in_file pipeline."""

from types import SimpleNamespace

import classify_tests_in_file

_run = getattr(classify_tests_in_file, "_run")


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


def _make_classifier(*triples):
    """Build per-test classifier from (test_name, prefix, clause) triples."""
    lookup = {n: {"prefix": p, "clause": c, "rationale": "r"}
              for n, p, c in triples}

    def classifier(prompt):
        for name, resp in lookup.items():
            if name in prompt:
                return resp
        return {"prefix": "test_non_lrm_", "clause": "non-lrm",
                "non_lrm_topic": "misc", "rationale": "fallback"}

    return classifier


def _make_classifier_with_topic(_name, prefix, clause, topic):
    """Build per-test classifier that includes non_lrm_topic."""
    resp = {"prefix": prefix, "clause": clause,
            "non_lrm_topic": topic, "rationale": "r"}

    def classifier(_prompt):
        return resp

    return classifier


def _stub_externals(monkeypatch, tmp_path, classifier):
    """Stub Claude CLI and CMake path."""
    monkeypatch.setattr(classify_tests_in_file, "_call_claude", classifier)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n", encoding="utf-8",
    )
    monkeypatch.setattr(classify_tests_in_file, "CMAKE_PATH", cmake)


def _run_pipeline(tmp_path, test, dry_run=False):
    """Execute _run on test_input.cpp in *tmp_path*."""
    _run(SimpleNamespace(
        file=str(tmp_path / "test_input.cpp"),
        output_dir=str(tmp_path),
        dry_run=dry_run,
        lrm=str(tmp_path / "lrm.txt"),
        arch=str(tmp_path / "arch.md"),
        test=test,
    ))


def _do_multi_clause(tmp_path, monkeypatch):
    """Write two tests, classify to different clauses, and run pipeline."""
    _write_input(
        tmp_path,
        "TEST(S, Alpha) {\n  EXPECT_TRUE(true);\n}\n\n"
        "TEST(S, Beta) {\n  EXPECT_EQ(1, 1);\n}\n\n",
    )
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("Alpha", "test_parser_", "6.1"),
        ("Beta", "test_lexer_", "5.3"),
    ))
    _run_pipeline(tmp_path, test="Alpha")
    _run_pipeline(tmp_path, test="Beta")
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
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("Fresh", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, test="Fresh")
    return existing


def _do_dry_run(tmp_path, monkeypatch):
    """Run pipeline in dry-run mode, return tmp_path."""
    _write_input(tmp_path, "TEST(S, DryT) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("DryT", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, test="DryT", dry_run=True)
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


# ---- Merge into existing file ----------------------------------------------


def test_merge_adds_new_test(tmp_path, monkeypatch):
    """Merged file contains the new test."""
    assert "TEST(S, Fresh)" in _do_merge(tmp_path, monkeypatch).read_text()


def test_merge_preserves_old_test(tmp_path, monkeypatch):
    """Merged file still contains the pre-existing test."""
    assert "TEST(S, Old)" in _do_merge(tmp_path, monkeypatch).read_text()


# ---- Deduplication ---------------------------------------------------------


def test_dedup_reports_duplicate(tmp_path, monkeypatch, capsys):
    """Tests already in the target file are reported as removed."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "TEST(S, Dup) {\n}\n", encoding="utf-8",
    )
    _write_input(tmp_path, "TEST(S, Dup) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("Dup", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, test="Dup")
    assert "Removed Dup" in capsys.readouterr().out


# ---- Non-LRM topic routing ------------------------------------------------


def test_non_lrm_topic_creates_named_file(tmp_path, monkeypatch):
    """Non-LRM test with topic creates test_non_lrm_<topic>.cpp."""
    _write_input(tmp_path, "TEST(S, InternalHelper) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _make_classifier_with_topic(
        "InternalHelper", "test_non_lrm_", "non-lrm", "aig",
    ))
    _run_pipeline(tmp_path, test="InternalHelper")
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


# ---- Self-named source (dedup regression) ---------------------------------


def test_self_named_source_not_treated_as_duplicate(tmp_path, monkeypatch):
    """Source file whose name matches target is not flagged as duplicate."""
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n\nnamespace {\n\n"
        "TEST(S, Keeper) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    _stub_externals(monkeypatch, tmp_path, _make_classifier_with_topic(
        "Keeper", "test_non_lrm_", "non-lrm", "aig",
    ))
    _run(SimpleNamespace(
        file=str(src), output_dir=str(tmp_path), dry_run=False,
        lrm=str(tmp_path / "lrm.txt"), arch=str(tmp_path / "arch.md"),
        test="Keeper",
    ))
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


# ---- Annex routing ---------------------------------------------------------


def test_annex_creates_annex_file(tmp_path, monkeypatch):
    """Annex-clause test creates test_<prefix>_annex_<letter>_<padded>.cpp."""
    _write_input(tmp_path, "TEST(S, GrammarRule) {\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("GrammarRule", "test_parser_", "A.6.3"),
    ))
    _run_pipeline(tmp_path, test="GrammarRule")
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
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("T", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, test="T")
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
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("QuotedTest", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, test="QuotedTest")
    assert "A module declaration" not in (
        tmp_path / "test_parser_clause_06_01.cpp"
    ).read_text()


# ---- Roundtrip parse -------------------------------------------------------


def test_output_reparseable(tmp_path, monkeypatch):
    """Generated output can be re-parsed by parse_file without errors."""
    _write_input(tmp_path, "TEST(S, Round) {\n  int x = 1;\n}\n\n")
    _stub_externals(monkeypatch, tmp_path, _make_classifier(
        ("Round", "test_parser_", "6.1"),
    ))
    _run_pipeline(tmp_path, test="Round")
    assert len(classify_tests_in_file.parse_file(
        tmp_path / "test_parser_clause_06_01.cpp",
    ).all_tests) == 1


# ---- Named namespace wrapper -----------------------------------------------


def _do_named_ns(tmp_path, monkeypatch):
    """Write input with namespace delta { ... } and run pipeline."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\n"
        "#include \"simulation/vpi.h\"\n\n"
        "namespace delta {\n"
        "namespace {\n\n"
        "TEST(NonLrmVpi, DefaultCtx) {\n"
        "  EXPECT_TRUE(true);\n"
        "}\n\n"
        "}  // namespace\n"
        "}  // namespace delta\n",
        encoding="utf-8",
    )
    _stub_externals(monkeypatch, tmp_path, _make_classifier_with_topic(
        "DefaultCtx", "test_non_lrm_", "non-lrm", "vpi",
    ))
    _run_pipeline(tmp_path, test="DefaultCtx")
    return tmp_path


def test_named_ns_creates_output(tmp_path, monkeypatch):
    """Pipeline creates output file from named-namespace input."""
    d = _do_named_ns(tmp_path, monkeypatch)
    assert (d / "test_non_lrm_vpi.cpp").exists()


def test_named_ns_output_contains_test(tmp_path, monkeypatch):
    """Output file contains the test from inside the named namespace."""
    d = _do_named_ns(tmp_path, monkeypatch)
    assert "TEST(NonLrmVpi, DefaultCtx)" in (
        d / "test_non_lrm_vpi.cpp"
    ).read_text()
