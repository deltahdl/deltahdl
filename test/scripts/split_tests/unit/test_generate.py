"""Unit tests for file generation functions in split_tests."""

import subprocess
from unittest.mock import MagicMock

import split_tests
from helpers import make_parsed_file as _parsed
from helpers import make_test_block as _tb


# ---- find_existing_tests ---------------------------------------------------


def test_find_existing_tests_empty(tmp_path):
    """Returns empty set when no matching files exist."""
    assert split_tests.find_existing_tests(
        "test_parser_clause_06", tmp_path,
    ) == set()


def test_find_existing_tests_exact(tmp_path):
    """Finds tests in exact match file."""
    f = tmp_path / "test_parser_clause_06.cpp"
    f.write_text("TEST(S, Existing) {\n}\n")
    result = split_tests.find_existing_tests(
        "test_parser_clause_06", tmp_path,
    )
    assert "Existing" in result


def test_find_existing_tests_variant(tmp_path):
    """Finds tests in variant files (e.g., _a.cpp)."""
    f = tmp_path / "test_parser_clause_06_a.cpp"
    f.write_text("TEST_F(S, Found) {\n}\n")
    result = split_tests.find_existing_tests(
        "test_parser_clause_06", tmp_path,
    )
    assert "Found" in result


def test_find_existing_tests_excludes_source(tmp_path):
    """Skips the source file when exclude_path is given."""
    f = tmp_path / "test_non_lrm_aig.cpp"
    f.write_text("TEST(S, Self) {\n}\n")
    result = split_tests.find_existing_tests(
        "test_non_lrm_aig", tmp_path, exclude_path=f,
    )
    assert "Self" not in result


# ---- clause_to_filename ----------------------------------------------------


def test_clause_to_filename_non_lrm_with_topic():
    """non-lrm:topic produces test_non_lrm_topic."""
    assert split_tests.clause_to_filename(
        "test_non_lrm_", "non-lrm:aig",
    ) == "test_non_lrm_aig"


def test_clause_to_filename_non_lrm_no_topic():
    """Plain non-lrm produces test_non_lrm_misc."""
    assert split_tests.clause_to_filename(
        "test_non_lrm_", "non-lrm",
    ) == "test_non_lrm_misc"


def test_clause_to_filename_annex():
    """Annex clause produces annex filename."""
    assert split_tests.clause_to_filename(
        "test_parser_", "A.6.3",
    ) == "test_parser_annex_a_06_03"


def test_clause_to_filename_regular():
    """Regular clause produces clause filename."""
    assert split_tests.clause_to_filename(
        "test_parser_", "6.3.1",
    ) == "test_parser_clause_06_03_01"


def test_clause_to_filename_trailing_underscore():
    """Prefix trailing underscore is stripped."""
    result = split_tests.clause_to_filename("test_parser_", "6.1")
    assert result == "test_parser_clause_06_01"


# ---- find_merge_target -----------------------------------------------------


def test_find_merge_target_exact(tmp_path):
    """Returns exact file when it exists."""
    f = tmp_path / "test_parser_clause_06.cpp"
    f.write_text("")
    assert split_tests.find_merge_target(
        "test_parser_clause_06", tmp_path,
    ) == f


def test_find_merge_target_variant(tmp_path):
    """Returns last variant file when exact does not exist."""
    (tmp_path / "test_parser_clause_06_a.cpp").write_text("")
    (tmp_path / "test_parser_clause_06_b.cpp").write_text("")
    result = split_tests.find_merge_target(
        "test_parser_clause_06", tmp_path,
    )
    assert result.name == "test_parser_clause_06_b.cpp"


def test_find_merge_target_none(tmp_path):
    """Returns None when no matching files exist."""
    assert split_tests.find_merge_target(
        "test_parser_clause_06", tmp_path,
    ) is None


def test_find_merge_target_excludes_source(tmp_path):
    """Returns None when only match is the excluded source file."""
    f = tmp_path / "test_non_lrm_aig.cpp"
    f.write_text("TEST(S, Self) {\n}\n")
    assert split_tests.find_merge_target(
        "test_non_lrm_aig", tmp_path, exclude_path=f,
    ) is None


# ---- load_lrm_titles -------------------------------------------------------


def test_load_lrm_titles_missing(monkeypatch, tmp_path):
    """Returns empty dict when LRM file is missing."""
    monkeypatch.setattr(split_tests, "LRM_PATH", tmp_path / "no.txt")
    assert not split_tests.load_lrm_titles()


def test_load_lrm_titles_clause(monkeypatch, tmp_path):
    """Parses numeric clauses from LRM."""
    lrm = tmp_path / "LRM.txt"
    lrm.write_text("6.3 Data types\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "LRM_PATH", lrm)
    assert split_tests.load_lrm_titles()["6.3"] == "Data types"


def test_load_lrm_titles_annex(monkeypatch, tmp_path):
    """Parses annex clauses from LRM."""
    lrm = tmp_path / "LRM.txt"
    lrm.write_text("A.6.3 Grammar stuff\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "LRM_PATH", lrm)
    assert split_tests.load_lrm_titles()["A.6.3"] == "Grammar stuff"


def test_load_lrm_titles_non_matching(monkeypatch, tmp_path):
    """Non-matching lines are skipped."""
    lrm = tmp_path / "LRM.txt"
    lrm.write_text("This is not a clause\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "LRM_PATH", lrm)
    assert not split_tests.load_lrm_titles()


# ---- strip_lrm_quotes ------------------------------------------------------


def test_strip_lrm_quotes_no_quote():
    """Returns line unchanged when no quote present."""
    assert split_tests.strip_lrm_quotes("int x = 0;") == "int x = 0;"


def test_strip_lrm_quotes_section_ref():
    """Strips quote but keeps section reference."""
    result = split_tests.strip_lrm_quotes(
        '// \u00a76.3: "A type is defined..."',
    )
    assert result == "// \u00a76.3:"


def test_strip_lrm_quotes_no_section_ref():
    """Returns empty string when quote has no section reference."""
    result = split_tests.strip_lrm_quotes(
        '// "All types must be..."',
    )
    assert result == ""


# ---- generate_file ---------------------------------------------------------


def test_generate_file_non_lrm():
    """Generates non-LRM file header."""
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = split_tests.generate_file("non-lrm", "", parsed, [t])
    assert content.startswith("// Non-LRM tests")


def test_generate_file_annex_with_title():
    """Generates annex header with title."""
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = split_tests.generate_file("A.6", "Grammar", parsed, [t])
    assert "// Annex A.6: Grammar" in content


def test_generate_file_annex_no_title():
    """Generates annex header without title."""
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = split_tests.generate_file("A.6", "", parsed, [t])
    assert "// Annex A.6" in content


def test_generate_file_regular_with_title():
    """Generates regular clause header with title."""
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = split_tests.generate_file("6.3", "Data types", parsed, [t])
    assert "// \u00a76.3: Data types" in content


def test_generate_file_regular_no_title():
    """Generates regular clause header without title."""
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert "// \u00a76.3" in content


def test_generate_file_with_using():
    """Includes using-line when present."""
    parsed = _parsed(using="using namespace delta;")
    t = _tb("T", comments=[])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert "using namespace delta;" in content


def test_generate_file_with_preamble():
    """Includes global preamble items."""
    pre = split_tests.PreambleItem(lines=["struct Foo {", "};"])
    parsed = _parsed(preamble=[pre])
    t = _tb("T", comments=[])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert "struct Foo {" in content


def test_generate_file_preceding_comments():
    """Includes preceding comments for tests."""
    parsed = _parsed()
    t = _tb("T", comments=["// a test comment"])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert "// a test comment" in content


def test_generate_file_preceding_comment_stripped():
    """Strips LRM quotes from preceding comments."""
    parsed = _parsed()
    t = _tb("T", comments=['// "All modules are..."'])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert '"All modules' not in content


def test_generate_file_namespace_wrapper():
    """Output includes namespace { ... } // namespace."""
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert "namespace {" in content and "}  // namespace" in content


def test_generate_file_preamble_stripped_empty():
    """Exercise generate_file preamble with strip_lrm_quotes returning empty."""
    pre = split_tests.PreambleItem(
        lines=['// "All types are..."'],
    )
    parsed = _parsed(preamble=[pre])
    t = _tb("T", comments=[])
    content = split_tests.generate_file("6.3", "", parsed, [t])
    assert "All types" not in content


# ---- append_tests_to_file --------------------------------------------------


def test_append_tests_to_file_basic(tmp_path):
    """Appends tests before } // namespace."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n"
        "\n"
        "namespace {\n"
        "\n"
        "TEST(S, Old) {\n"
        "}\n"
        "\n"
        "}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("New", comments=[])
    split_tests.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "TEST(S, New)" in text


def _append_with_preamble(tmp_path, existing_content):
    """Write existing_content, append a preamble + test, return file text."""
    f = tmp_path / "existing.cpp"
    f.write_text(existing_content, encoding="utf-8")
    pre = split_tests.PreambleItem(lines=["struct Bar {", "};"])
    t = _tb("T", comments=[])
    split_tests.append_tests_to_file(f, [pre], [t])
    return f.read_text(encoding="utf-8")


def test_append_tests_to_file_new_preamble(tmp_path):
    """Appends preamble items that are not already present."""
    text = _append_with_preamble(
        tmp_path, "namespace {\n}  // namespace\n"
    )
    assert "struct Bar {" in text


def test_append_tests_to_file_duplicate_preamble(tmp_path):
    """Skips preamble items already present in the file."""
    text = _append_with_preamble(
        tmp_path, "struct Bar {\n};\nnamespace {\n}  // namespace\n"
    )
    assert text.count("struct Bar {") == 1


def test_append_tests_to_file_no_namespace_close(tmp_path):
    """Appends at end of file when no } // namespace found."""
    f = tmp_path / "existing.cpp"
    f.write_text("int x = 0;\n", encoding="utf-8")
    t = _tb("T", comments=[])
    split_tests.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "TEST(S, T)" in text


def test_append_tests_to_file_comment_strip(tmp_path):
    """Strips LRM quotes from appended preceding comments."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("T", comments=['// "All modules..."'])
    split_tests.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert '"All modules' not in text


def test_append_tests_to_file_comment_only_preamble(tmp_path):
    """Preamble with only comment lines uses first line for dedup check."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    pre = split_tests.PreambleItem(lines=["// A helper comment"])
    t = _tb("T", comments=[])
    split_tests.append_tests_to_file(f, [pre], [t])
    text = f.read_text(encoding="utf-8")
    assert "// A helper comment" in text


def test_append_tests_to_file_single_space_close(tmp_path):
    """Finds '} // namespace' (single space variant)."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n"
        "TEST(S, Old) {\n}\n"
        "} // namespace\n",
        encoding="utf-8",
    )
    t = _tb("New", comments=[])
    split_tests.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "TEST(S, New)" in text


def test_append_tests_to_file_empty_stripped_comment(tmp_path):
    """Empty stripped preceding comment is not appended."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("T", comments=['// "Some LRM quote..."'])
    split_tests.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "Some LRM quote" not in text


def test_append_tests_to_file_normal_comment(tmp_path):
    """Non-LRM preceding comment is appended by append_tests_to_file."""
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("T", comments=["// normal comment"])
    split_tests.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "// normal comment" in text


# ---- update_cmake ----------------------------------------------------------


def test_update_cmake_removes_and_adds(monkeypatch, tmp_path):
    """Removes old test name and adds new ones."""
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(old_test)\n"
        "add_unit_test(keep_test)\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    split_tests.update_cmake("old_test", ["new_a", "new_b"])
    text = cmake.read_text(encoding="utf-8")
    assert "old_test" not in text and "new_a" in text


def test_update_cmake_sorted(monkeypatch, tmp_path):
    """New entries are sorted and deduplicated."""
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(z_test)\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(split_tests, "CMAKE_PATH", cmake)
    split_tests.update_cmake("old", ["a_test"])
    text = cmake.read_text(encoding="utf-8")
    assert text.index("a_test") < text.index("z_test")


# ---- update_standalone -----------------------------------------------------


def test_update_standalone_missing(monkeypatch, tmp_path):
    """Does nothing when STANDALONE.md is missing."""
    monkeypatch.setattr(
        split_tests, "STANDALONE_PATH", tmp_path / "no.md",
    )
    split_tests.update_standalone("test_x")
    assert not (tmp_path / "no.md").exists()


def test_update_standalone_removes_entry(monkeypatch, tmp_path):
    """Removes the matching entry line."""
    sa = tmp_path / "STANDALONE.md"
    sa.write_text(
        "- [ ] test_x\n- [ ] test_y\n", encoding="utf-8",
    )
    monkeypatch.setattr(split_tests, "STANDALONE_PATH", sa)
    split_tests.update_standalone("test_x")
    text = sa.read_text(encoding="utf-8")
    assert "test_x" not in text and "test_y" in text


# ---- commit_and_push -------------------------------------------------------


def test_commit_and_push_zero_files(monkeypatch):
    """Uses 'Remove' message for zero files."""
    calls = []
    monkeypatch.setattr(
        subprocess, "run",
        lambda *a, **_kw: (
            calls.append(a[0]), MagicMock(returncode=0),
        )[1],
    )
    split_tests.commit_and_push("test_x", 0)
    assert any("Remove" in " ".join(c) for c in calls if "commit" in c)


def test_commit_and_push_nonzero_files(monkeypatch):
    """Uses 'Split' message for non-zero files."""
    calls = []
    monkeypatch.setattr(
        subprocess, "run",
        lambda *a, **_kw: (
            calls.append(a[0]), MagicMock(returncode=0),
        )[1],
    )
    split_tests.commit_and_push("test_x", 3)
    assert any("Split" in " ".join(c) for c in calls if "commit" in c)


def test_commit_and_push_push_fail(monkeypatch, capsys):
    """Prints warning when git push fails."""
    def mock_run(*a, **_kw):
        """Simulate git push failure."""
        r = MagicMock()
        r.returncode = 1 if "push" in a[0] else 0
        return r

    monkeypatch.setattr(subprocess, "run", mock_run)
    split_tests.commit_and_push("test_x", 1)
    assert "WARNING: git push failed" in capsys.readouterr().out
