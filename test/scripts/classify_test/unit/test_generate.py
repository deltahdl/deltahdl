"""Unit tests for file generation functions in classify_test."""


# ---- find_existing_tests ---------------------------------------------------


def test_find_existing_tests_empty(ct, tmp_path):
    """Returns empty set when no matching files exist."""
    assert ct.find_existing_tests(
        "test_parser_clause_06", tmp_path,
    ) == set()


def test_find_existing_tests_exact(ct, tmp_path):
    """Finds tests in exact match file."""
    f = tmp_path / "test_parser_clause_06.cpp"
    f.write_text("TEST(S, Existing) {\n}\n")
    result = ct.find_existing_tests(
        "test_parser_clause_06", tmp_path,
    )
    assert "Existing" in result


def test_find_existing_tests_variant(ct, tmp_path):
    """Finds tests in variant files (e.g., _a.cpp)."""
    f = tmp_path / "test_parser_clause_06_a.cpp"
    f.write_text("TEST_F(S, Found) {\n}\n")
    result = ct.find_existing_tests(
        "test_parser_clause_06", tmp_path,
    )
    assert "Found" in result


def test_find_existing_tests_excludes_source(ct, tmp_path):
    """Skips the source file when exclude_path is given."""
    f = tmp_path / "test_non_lrm_aig.cpp"
    f.write_text("TEST(S, Self) {\n}\n")
    result = ct.find_existing_tests(
        "test_non_lrm_aig", tmp_path, exclude_path=f,
    )
    assert "Self" not in result


# ---- clause_to_filename ----------------------------------------------------


def test_clause_to_filename_non_lrm_with_topic(ct):
    """non-lrm:topic produces test_non_lrm_topic."""
    assert ct.clause_to_filename(
        "test_non_lrm_", "non-lrm:aig",
    ) == "test_non_lrm_aig"


def test_clause_to_filename_non_lrm_no_topic(ct):
    """Plain non-lrm produces test_non_lrm_misc."""
    assert ct.clause_to_filename(
        "test_non_lrm_", "non-lrm",
    ) == "test_non_lrm_misc"


def test_clause_to_filename_annex(ct):
    """Annex clause produces annex filename."""
    assert ct.clause_to_filename(
        "test_parser_", "A.6.3",
    ) == "test_parser_annex_a_06_03"


def test_clause_to_filename_bare_annex(ct):
    """Bare annex letter produces annex filename."""
    assert ct.clause_to_filename(
        "test_lexer_", "B",
    ) == "test_lexer_annex_b"


def test_clause_to_filename_regular(ct):
    """Regular clause produces clause filename."""
    assert ct.clause_to_filename(
        "test_parser_", "6.3.1",
    ) == "test_parser_clause_06_03_01"


def test_clause_to_filename_trailing_underscore(ct):
    """Prefix trailing underscore is stripped."""
    result = ct.clause_to_filename("test_parser_", "6.1")
    assert result == "test_parser_clause_06_01"


# ---- _count_file_lines -----------------------------------------------------


def test_count_file_lines(ct, tmp_path):
    """Returns line count of an existing file."""
    _count_file_lines = getattr(ct, "_count_file_lines")
    f = tmp_path / "test.cpp"
    f.write_text("a\nb\nc\n", encoding="utf-8")
    assert _count_file_lines(f) == 3


def test_count_file_lines_missing(ct, tmp_path):
    """Returns 0 for nonexistent file."""
    _count_file_lines = getattr(ct, "_count_file_lines")
    assert _count_file_lines(tmp_path / "missing.cpp") == 0


# ---- _next_suffix_file -----------------------------------------------------


def test_next_suffix_file_no_existing(ct, tmp_path):
    """Returns '_a' when no suffix files exist."""
    _next_suffix_file = getattr(ct, "_next_suffix_file")
    assert _next_suffix_file("test_parser_clause_06", tmp_path) == "a"


def test_next_suffix_file_a_exists(ct, tmp_path):
    """Returns '_b' when _a exists."""
    _next_suffix_file = getattr(ct, "_next_suffix_file")
    (tmp_path / "test_parser_clause_06_a.cpp").write_text("")
    assert _next_suffix_file("test_parser_clause_06", tmp_path) == "b"


def test_next_suffix_file_multiple(ct, tmp_path):
    """Returns '_c' when _a and _b exist."""
    _next_suffix_file = getattr(ct, "_next_suffix_file")
    (tmp_path / "test_parser_clause_06_a.cpp").write_text("")
    (tmp_path / "test_parser_clause_06_b.cpp").write_text("")
    assert _next_suffix_file("test_parser_clause_06", tmp_path) == "c"


# ---- _rename_base_to_suffix ------------------------------------------------


def test_rename_base_to_suffix_returns_a(ct, tmp_path):
    """Returned path has _a suffix when no suffixes exist."""
    _rename_base_to_suffix = getattr(ct, "_rename_base_to_suffix")
    f = tmp_path / "foo.cpp"
    f.write_text("content")
    result = _rename_base_to_suffix("foo", tmp_path)
    assert result.name == "foo_a.cpp"


def test_rename_base_to_suffix_removes_base(ct, tmp_path):
    """Base file no longer exists after rename."""
    _rename_base_to_suffix = getattr(ct, "_rename_base_to_suffix")
    f = tmp_path / "foo.cpp"
    f.write_text("content")
    _rename_base_to_suffix("foo", tmp_path)
    assert not f.exists()


def test_rename_base_to_suffix_creates_target(ct, tmp_path):
    """Target _a file exists after rename."""
    _rename_base_to_suffix = getattr(ct, "_rename_base_to_suffix")
    f = tmp_path / "foo.cpp"
    f.write_text("content")
    _rename_base_to_suffix("foo", tmp_path)
    assert (tmp_path / "foo_a.cpp").exists()


def test_rename_base_to_suffix_skips_existing_variant(ct, tmp_path):
    """Renames base to _b when _a already exists."""
    _rename_base_to_suffix = getattr(ct, "_rename_base_to_suffix")
    (tmp_path / "foo.cpp").write_text("base")
    (tmp_path / "foo_a.cpp").write_text("variant a")
    result = _rename_base_to_suffix("foo", tmp_path)
    assert result.name == "foo_b.cpp"


def test_rename_base_to_suffix_preserves_content(ct, tmp_path):
    """Renamed file preserves original content."""
    _rename_base_to_suffix = getattr(ct, "_rename_base_to_suffix")
    (tmp_path / "foo.cpp").write_text("base")
    (tmp_path / "foo_a.cpp").write_text("variant a")
    _rename_base_to_suffix("foo", tmp_path)
    assert (tmp_path / "foo_b.cpp").read_text() == "base"


# ---- find_merge_target -----------------------------------------------------


def test_find_merge_target_exact(ct, tmp_path):
    """Returns exact file when it exists."""
    f = tmp_path / "test_parser_clause_06.cpp"
    f.write_text("")
    assert ct.find_merge_target(
        "test_parser_clause_06", tmp_path,
    ) == f


def test_find_merge_target_variant(ct, tmp_path):
    """Returns last variant file when exact does not exist."""
    (tmp_path / "test_parser_clause_06_a.cpp").write_text("")
    (tmp_path / "test_parser_clause_06_b.cpp").write_text("")
    result = ct.find_merge_target(
        "test_parser_clause_06", tmp_path,
    )
    assert result.name == "test_parser_clause_06_b.cpp"


def test_find_merge_target_none(ct, tmp_path):
    """Returns None when no matching files exist."""
    assert ct.find_merge_target(
        "test_parser_clause_06", tmp_path,
    ) is None


def test_find_merge_target_excludes_source(ct, tmp_path):
    """Returns None when only match is the excluded source file."""
    f = tmp_path / "test_non_lrm_aig.cpp"
    f.write_text("TEST(S, Self) {\n}\n")
    assert ct.find_merge_target(
        "test_non_lrm_aig", tmp_path, exclude_path=f,
    ) is None


# ---- strip_lrm_quotes ------------------------------------------------------


def test_strip_lrm_quotes_no_quote(ct):
    """Returns line unchanged when no quote present."""
    assert ct.strip_lrm_quotes("int x = 0;") == "int x = 0;"


def test_strip_lrm_quotes_section_ref(ct):
    """Strips quote but keeps section reference."""
    result = ct.strip_lrm_quotes(
        '// \u00a76.3: "A type is defined..."',
    )
    assert result == "// \u00a76.3:"


def test_strip_lrm_quotes_no_section_ref(ct):
    """Returns empty string when quote has no section reference."""
    result = ct.strip_lrm_quotes(
        '// "All types must be..."',
    )
    assert result == ""


# ---- generate_file ---------------------------------------------------------


def test_generate_file_non_lrm(ct, ct_helpers):
    """Generates non-LRM file header."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = ct.generate_file("non-lrm", "", parsed, [t])
    assert content.startswith("// Non-LRM tests")


def test_generate_file_annex_with_title(ct, ct_helpers):
    """Generates annex header with title."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = ct.generate_file("A.6", "Grammar", parsed, [t])
    assert "// Annex A.6: Grammar" in content


def test_generate_file_annex_no_title(ct, ct_helpers):
    """Generates annex header without title."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = ct.generate_file("A.6", "", parsed, [t])
    assert "// Annex A.6" in content


def test_generate_file_regular_with_title(ct, ct_helpers):
    """Generates regular clause header with title."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = ct.generate_file("6.3", "Data types", parsed, [t])
    assert "// \u00a76.3: Data types" in content


def test_generate_file_regular_no_title(ct, ct_helpers):
    """Generates regular clause header without title."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "// \u00a76.3" in content


def test_generate_file_with_using(ct, ct_helpers):
    """Includes using-line when present."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed(using="using namespace delta;")
    t = _tb("T", comments=[])
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "using namespace delta;" in content


def test_generate_file_with_preamble(ct, ct_helpers):
    """Includes global preamble items referenced by tests."""
    _parsed = ct_helpers.make_parsed_file
    pre = ct.PreambleItem(lines=["struct Foo {", "};"])
    parsed = _parsed(preamble=[pre])
    t = ct.TestBlock(
        suite_name="S", test_name="T",
        lines=["TEST(S, T) {", "  Foo f;", "}"],
        preceding_comments=[],
    )
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "struct Foo {" in content


def test_generate_file_preceding_comments(ct, ct_helpers):
    """Includes preceding comments for tests."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=["// a test comment"])
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "// a test comment" in content


def test_generate_file_preceding_comment_stripped(ct, ct_helpers):
    """Strips LRM quotes from preceding comments."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=['// "All modules are..."'])
    content = ct.generate_file("6.3", "", parsed, [t])
    assert '"All modules' not in content


def test_generate_file_namespace_wrapper(ct, ct_helpers):
    """Output includes namespace { ... } // namespace."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    parsed = _parsed()
    t = _tb("T", comments=[])
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "namespace {" in content and "}  // namespace" in content


def test_generate_file_with_section_preamble(ct, ct_helpers):
    """Includes section preamble items referenced by tests."""
    _parsed = ct_helpers.make_parsed_file
    sec = ct.PreambleItem(
        lines=["static int Helper() {", "  return 42;", "}"],
    )
    parsed = _parsed()
    parsed.section_preamble = [sec]
    t = ct.TestBlock(
        suite_name="S", test_name="T",
        lines=["TEST(S, T) {", "  Helper();", "}"],
        preceding_comments=[],
    )
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "static int Helper() {" in content


def test_generate_file_preamble_stripped_empty(ct, ct_helpers):
    """Exercise generate_file preamble with strip_lrm_quotes returning empty."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    pre = ct.PreambleItem(
        lines=['// "All types are..."'],
    )
    parsed = _parsed(preamble=[pre])
    t = _tb("T", comments=[])
    content = ct.generate_file("6.3", "", parsed, [t])
    assert "All types" not in content


# ---- append_tests_to_file --------------------------------------------------


def test_append_tests_to_file_basic(ct, ct_helpers, tmp_path):
    """Appends tests before } // namespace."""
    _tb = ct_helpers.make_test_block
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
    ct.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "TEST(S, New)" in text


def _append_with_preamble(ct, ct_helpers, tmp_path, existing_content):
    """Write existing_content, append a preamble + test, return file text."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(existing_content, encoding="utf-8")
    pre = ct.PreambleItem(lines=["struct Bar {", "};"])
    t = _tb("T", comments=[])
    ct.append_tests_to_file(f, [pre], [t])
    return f.read_text(encoding="utf-8")


def test_append_tests_to_file_new_preamble(ct, ct_helpers, tmp_path):
    """Appends preamble items that are not already present."""
    text = _append_with_preamble(
        ct, ct_helpers, tmp_path, "namespace {\n}  // namespace\n"
    )
    assert "struct Bar {" in text


def test_append_tests_to_file_duplicate_preamble(ct, ct_helpers, tmp_path):
    """Skips preamble items already present in the file."""
    text = _append_with_preamble(
        ct, ct_helpers, tmp_path,
        "struct Bar {\n};\nnamespace {\n}  // namespace\n",
    )
    assert text.count("struct Bar {") == 1


def test_append_tests_to_file_no_namespace_close(ct, ct_helpers, tmp_path):
    """Appends at end of file when no } // namespace found."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text("int x = 0;\n", encoding="utf-8")
    t = _tb("T", comments=[])
    ct.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "TEST(S, T)" in text


def test_append_tests_to_file_comment_strip(ct, ct_helpers, tmp_path):
    """Strips LRM quotes from appended preceding comments."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("T", comments=['// "All modules..."'])
    ct.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert '"All modules' not in text


def test_append_tests_to_file_comment_only_preamble(ct, ct_helpers, tmp_path):
    """Preamble with only comment lines uses first line for dedup check."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    pre = ct.PreambleItem(lines=["// A helper comment"])
    t = _tb("T", comments=[])
    ct.append_tests_to_file(f, [pre], [t])
    text = f.read_text(encoding="utf-8")
    assert "// A helper comment" in text


def test_append_tests_to_file_single_space_close(ct, ct_helpers, tmp_path):
    """Finds '} // namespace' (single space variant)."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n"
        "TEST(S, Old) {\n}\n"
        "} // namespace\n",
        encoding="utf-8",
    )
    t = _tb("New", comments=[])
    ct.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "TEST(S, New)" in text


def test_append_tests_to_file_empty_stripped_comment(ct, ct_helpers, tmp_path):
    """Empty stripped preceding comment is not appended."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("T", comments=['// "Some LRM quote..."'])
    ct.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "Some LRM quote" not in text


def test_append_tests_to_file_normal_comment(ct, ct_helpers, tmp_path):
    """Non-LRM preceding comment is appended by append_tests_to_file."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("T", comments=["// normal comment"])
    ct.append_tests_to_file(f, [], [t])
    text = f.read_text(encoding="utf-8")
    assert "// normal comment" in text


# ---- _write_files splitting -------------------------------------------------


def _make_large_test(ct, name, n_lines):
    """Create a test block with n_lines of body."""
    body = [f"TEST(S, {name}) {{"]
    for i in range(n_lines - 2):
        body.append(f"  int x{i} = {i};")
    body.append("}")
    return ct.TestBlock(
        suite_name="S",
        test_name=name,
        lines=body,
        preceding_comments=[],
    )


def _do_split_write(ct, ct_helpers, tmp_path):
    """Helper: write two large tests with max_lines=50."""
    _parsed = ct_helpers.make_parsed_file
    _write_files = getattr(ct, "_write_files")
    parsed = _parsed()
    t1 = _make_large_test(ct, "Big1", 40)
    t2 = _make_large_test(ct, "Big2", 40)
    to_create = [("test_parser_clause_06_01", "6.1", [t1, t2])]
    return _write_files(
        to_create, [], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}, "max_lines": 50},
    )


def test_write_files_split_creates_a(ct, ct_helpers, tmp_path):
    """Splitting creates _a suffix file."""
    _do_split_write(ct, ct_helpers, tmp_path)
    assert (tmp_path / "test_parser_clause_06_01_a.cpp").exists()


def test_write_files_split_creates_b(ct, ct_helpers, tmp_path):
    """Splitting creates _b suffix file."""
    _do_split_write(ct, ct_helpers, tmp_path)
    assert (tmp_path / "test_parser_clause_06_01_b.cpp").exists()


def test_write_files_split_no_base(ct, ct_helpers, tmp_path):
    """Splitting does not create unsuffixed base file."""
    _do_split_write(ct, ct_helpers, tmp_path)
    assert not (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_write_files_split_returns_names(ct, ct_helpers, tmp_path):
    """Splitting returns both suffix names."""
    names = _do_split_write(ct, ct_helpers, tmp_path)
    assert "test_parser_clause_06_01_a" in names


def test_write_files_no_split_under_max_lines(ct, ct_helpers, tmp_path):
    """Content under limit stays in one file."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    _write_files = getattr(ct, "_write_files")
    parsed = _parsed()
    t = _tb("Small", comments=[])
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _write_files(
        to_create, [], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}, "max_lines": 500},
    )
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_write_files_no_split_returns_name(ct, ct_helpers, tmp_path):
    """No-split returns the base name."""
    _parsed = ct_helpers.make_parsed_file
    _tb = ct_helpers.make_test_block
    _write_files = getattr(ct, "_write_files")
    parsed = _parsed()
    t = _tb("Small", comments=[])
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    names = _write_files(
        to_create, [], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}, "max_lines": 500},
    )
    assert "test_parser_clause_06_01" in names


def test_write_files_no_split_when_no_max_lines(ct, ct_helpers, tmp_path):
    """max_lines=None never splits."""
    _parsed = ct_helpers.make_parsed_file
    _write_files = getattr(ct, "_write_files")
    parsed = _parsed()
    t1 = _make_large_test(ct, "Big1", 40)
    t2 = _make_large_test(ct, "Big2", 40)
    to_create = [("test_parser_clause_06_01", "6.1", [t1, t2])]
    _write_files(
        to_create, [], parsed,
        {"test_dir": tmp_path, "lrm_titles": {}},
    )
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


# ---- append_tests_to_file splitting ----------------------------------------


def _near_limit_file(tmp_path, name):
    """Create a file near the 50-line limit and return its path."""
    f = tmp_path / name
    lines = ["#include <gtest/gtest.h>", "", "namespace {", ""]
    for i in range(40):
        lines.append(f"// line {i}")
    lines.extend(["", "}  // namespace", ""])
    f.write_text("\n".join(lines), encoding="utf-8")
    return f


def test_append_splits_creates_overflow_file(ct, tmp_path):
    """Overflow tests go to next suffix file."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01_a.cpp")
    t = _make_large_test(ct, "Overflow", 20)
    ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    assert (tmp_path / "test_parser_clause_06_01_b.cpp").exists()


def test_append_splits_returns_new_name(ct, tmp_path):
    """Overflow append returns the new suffix filename."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01_a.cpp")
    t = _make_large_test(ct, "Overflow", 20)
    new_names = ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    assert "test_parser_clause_06_01_b" in new_names


def test_append_no_split_keeps_in_file(ct, ct_helpers, tmp_path):
    """Append stays in same file when under limit."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("New", comments=[])
    ct.append_tests_to_file(
        f, [], [t], max_lines=500,
    )
    assert "TEST(S, New)" in f.read_text(encoding="utf-8")


def test_append_no_split_returns_empty(ct, ct_helpers, tmp_path):
    """No-split append returns empty list."""
    _tb = ct_helpers.make_test_block
    f = tmp_path / "existing.cpp"
    f.write_text(
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    t = _tb("New", comments=[])
    new_names = ct.append_tests_to_file(
        f, [], [t], max_lines=500,
    )
    assert not new_names


def test_append_renames_base_to_a(ct, tmp_path):
    """Base file renamed to _a when splitting."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01.cpp")
    t = _make_large_test(ct, "Overflow", 20)
    ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    assert (tmp_path / "test_parser_clause_06_01_a.cpp").exists()


def test_append_renames_base_creates_overflow(ct, tmp_path):
    """Overflow goes to _b when base renamed to _a."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01.cpp")
    t = _make_large_test(ct, "Overflow", 20)
    ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    assert (tmp_path / "test_parser_clause_06_01_b.cpp").exists()


def test_append_renames_base_removes_original(ct, tmp_path):
    """Original base file no longer exists after rename."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01.cpp")
    t = _make_large_test(ct, "Overflow", 20)
    ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    assert not (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_append_renames_base_returns_both_names(ct, tmp_path):
    """Returns both _a and _b names when base is renamed."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01.cpp")
    t = _make_large_test(ct, "Overflow", 20)
    new_names = ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    assert "test_parser_clause_06_01_a" in new_names


def _do_multi_batch_overflow(ct, tmp_path):
    """Set up multi-batch overflow: 3 tests into near-limit file."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01_a.cpp")
    tests = [_make_large_test(ct, f"Ov{i}", 20) for i in range(3)]
    ct.append_tests_to_file(
        f, [], tests, max_lines=50,
    )


def test_append_overflow_multi_batch_creates_b(ct, tmp_path):
    """Multi-batch overflow creates _b suffix file."""
    _do_multi_batch_overflow(ct, tmp_path)
    assert (tmp_path / "test_parser_clause_06_01_b.cpp").exists()


def test_append_overflow_multi_batch_creates_c(ct, tmp_path):
    """Third overflow batch creates _c suffix file."""
    _do_multi_batch_overflow(ct, tmp_path)
    assert (tmp_path / "test_parser_clause_06_01_c.cpp").exists()


def test_append_overflow_includes_preceding_comments(ct, tmp_path):
    """Overflow file includes preceding comments from tests."""
    f = _near_limit_file(tmp_path, "test_parser_clause_06_01_a.cpp")
    t = ct.TestBlock(
        suite_name="S", test_name="Commented",
        lines=["TEST(S, Commented) {"]
        + [f"  int x{i} = {i};" for i in range(18)]
        + ["}"],
        preceding_comments=["// important comment"],
    )
    ct.append_tests_to_file(
        f, [], [t], max_lines=50,
    )
    overflow = tmp_path / "test_parser_clause_06_01_b.cpp"
    assert "// important comment" in overflow.read_text(encoding="utf-8")


# ---- _write_overflow_file edge cases ----------------------------------------


def test_write_overflow_file_strips_empty_comment(ct, ct_helpers, tmp_path):
    """Stripped LRM-quote comment is omitted from overflow file."""
    _write_overflow_file = getattr(ct, "_write_overflow_file")
    source = tmp_path / "source.cpp"
    source.write_text(
        "#include <gtest/gtest.h>\n\nnamespace {\n}  // namespace\n",
        encoding="utf-8",
    )
    out = tmp_path / "overflow.cpp"
    t = ct.TestBlock(
        suite_name="S", test_name="T",
        lines=["TEST(S, T) {", "}"],
        preceding_comments=['// "All modules are..."'],
    )
    _write_overflow_file(out, source, [t])
    assert "All modules" not in out.read_text(encoding="utf-8")


def test_write_overflow_file_no_namespace(ct, ct_helpers, tmp_path):
    """Copies entire source when no 'namespace {' found."""
    _write_overflow_file = getattr(ct, "_write_overflow_file")
    _tb = ct_helpers.make_test_block
    source = tmp_path / "source.cpp"
    source.write_text(
        "#include <gtest/gtest.h>\nint x = 0;\n", encoding="utf-8",
    )
    out = tmp_path / "overflow.cpp"
    t = _tb("T", comments=[])
    _write_overflow_file(out, source, [t])
    assert "int x = 0;" in out.read_text(encoding="utf-8")


# ---- _batch_tests edge cases ------------------------------------------------


def test_batch_tests_empty(ct):
    """Empty tests list produces empty batches."""
    _batch_tests = getattr(ct, "_batch_tests")
    assert not _batch_tests([], 10, 50)


# ---- _flush_overflow edge cases ---------------------------------------------


def test_flush_overflow_empty(ct, tmp_path):
    """Empty overflow list returns empty names."""
    _flush_overflow = getattr(ct, "_flush_overflow")
    source = tmp_path / "source.cpp"
    source.write_text("namespace {\n}  // namespace\n", encoding="utf-8")
    assert not _flush_overflow([], "base", tmp_path, source, 50)


# ---- update_cmake ----------------------------------------------------------


def test_update_cmake_removes_and_adds(ct, monkeypatch, tmp_path):
    """Removes old test name and adds new ones."""
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(old_test)\n"
        "add_unit_test(keep_test)\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    ct.update_cmake("old_test", ["new_a", "new_b"])
    text = cmake.read_text(encoding="utf-8")
    assert "old_test" not in text and "new_a" in text


def test_update_cmake_sorted(ct, monkeypatch, tmp_path):
    """New entries are sorted and deduplicated."""
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(z_test)\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    ct.update_cmake("old", ["a_test"])
    text = cmake.read_text(encoding="utf-8")
    assert text.index("a_test") < text.index("z_test")
