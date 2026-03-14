"""Unit tests for parsing functions in classify_test."""

from pathlib import Path

import pytest


# ---- find_repo_root --------------------------------------------------------


def test_find_repo_root_exits_when_no_repo_root(tmp_path, monkeypatch, ct):
    """find_repo_root exits when no test/CMakeLists.txt exists."""
    monkeypatch.setattr(Path, "cwd", staticmethod(lambda: tmp_path))
    with pytest.raises(SystemExit):
        ct.find_repo_root()


def test_find_repo_root_returns_repo_root(tmp_path, monkeypatch, ct):
    """find_repo_root returns the directory containing test/CMakeLists.txt."""
    (tmp_path / "test").mkdir()
    (tmp_path / "test" / "CMakeLists.txt").write_text("")
    child = tmp_path / "sub" / "deep"
    child.mkdir(parents=True)
    monkeypatch.setattr(Path, "cwd", staticmethod(lambda: child))
    assert ct.find_repo_root() == tmp_path


# ---- _update_brace_depth ---------------------------------------------------


def test_update_brace_depth_open_brace_increments(ct):
    """Opening brace increments depth."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    d, _, _, found = _update_brace_depth("{", 0, False, False)
    assert d == 1 and not found


def test_update_brace_depth_close_brace_at_one_returns_found(ct):
    """Closing brace at depth 1 returns found=True."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    d, _, _, found = _update_brace_depth("}", 1, False, False)
    assert d == 0 and found


def test_update_brace_depth_close_brace_non_zero_no_found(ct):
    """Closing brace when depth > 1 does not signal found."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    d, _, _, found = _update_brace_depth("}", 2, False, False)
    assert d == 1 and not found


def test_update_brace_depth_ignores_braces_in_string(ct):
    """Braces inside a string literal are ignored."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    d, ins, _, _ = _update_brace_depth(
        '"{"', 0, False, False,
    )
    assert d == 0 and not ins


def test_update_brace_depth_escape_in_string(ct):
    """Backslash inside a string skips the next character."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    d, ins, _, _ = _update_brace_depth(
        r'"\""', 0, False, False,
    )
    assert d == 0 and not ins


def test_update_brace_depth_line_comment(ct):
    """// comment causes remainder of line to be skipped."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    d, _, _, _ = _update_brace_depth(
        "// {", 0, False, False,
    )
    assert d == 0


def test_update_brace_depth_block_comment_start(ct):
    """/* starts a block comment."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    _, _, bc, _ = _update_brace_depth(
        "/* {", 0, False, False,
    )
    assert bc is True


def test_update_brace_depth_block_comment_end(ct):
    """*/ ends a block comment."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    _, _, bc, _ = _update_brace_depth(
        "*/", 0, False, True,
    )
    assert bc is False


def test_update_brace_depth_stays_in_block_comment(ct):
    """Non-closing chars inside block comment stay in comment."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    _, _, bc, _ = _update_brace_depth(
        "x y z", 0, False, True,
    )
    assert bc is True


def test_update_brace_depth_star_no_slash(ct):
    """A * not followed by / does not end a block comment."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    _, _, bc, _ = _update_brace_depth(
        "*x", 0, False, True,
    )
    assert bc is True


def test_update_brace_depth_empty_line(ct):
    """An empty line leaves state unchanged."""
    _update_brace_depth = getattr(ct, "_update_brace_depth")
    assert _update_brace_depth("", 0, False, False) == (
        0, False, False, False,
    )


# ---- extract_brace_block ---------------------------------------------------


def test_extract_brace_block_single_line(ct):
    """Extracts a simple single-line brace block."""
    _, end = ct.extract_brace_block(["{}\n"], 0)
    assert end == 0


def test_extract_brace_block_multi_line(ct):
    """Extracts a multi-line brace block."""
    lines = ["{\n", "  x;\n", "}\n"]
    block, end = ct.extract_brace_block(lines, 0)
    assert end == 2 and len(block) == 3


def test_extract_brace_block_unmatched(ct):
    """Raises ValueError for unmatched braces."""
    with pytest.raises(ValueError, match="Unmatched brace"):
        ct.extract_brace_block(["{\n"], 0)


# ---- is_section_header -----------------------------------------------------


def test_is_section_header_equals_banner(ct):
    """Lines with 10+ '=' are section headers."""
    assert ct.is_section_header("// ==========") is True


def test_is_section_header_dash_banner(ct):
    """Lines with 10+ '-' are section headers."""
    assert ct.is_section_header("// ----------") is True


def test_is_section_header_too_short(ct):
    """Fewer than 10 repeated chars is not a header."""
    assert ct.is_section_header("// ===") is False


def test_is_section_header_no_comment(ct):
    """A line not starting with // is not a header."""
    assert ct.is_section_header("==========") is False


def test_is_section_header_mixed(ct):
    """A mixed =- line is not a header."""
    assert ct.is_section_header("// ====------") is False


# ---- _parse_header ---------------------------------------------------------


def test_parse_header_full(ct):
    """Parses includes, using-line, and namespace."""
    _parse_header = getattr(ct, "_parse_header")
    lines = [
        "// comment\n",
        "#include <gtest/gtest.h>\n",
        "\n",
        "using namespace delta;\n",
        "\n",
        "namespace {\n",
        "body\n",
    ]
    _, _, has_ns, _ = _parse_header(lines)
    assert has_ns is True


def test_parse_header_no_using(ct):
    """Parses header without a using-line."""
    _parse_header = getattr(ct, "_parse_header")
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "namespace {\n",
    ]
    _, using, _, _ = _parse_header(lines)
    assert using is None


def test_parse_header_no_namespace(ct):
    """Parses header without namespace wrapper."""
    _parse_header = getattr(ct, "_parse_header")
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "TEST(S, T) {\n",
    ]
    _, _, has_ns, _ = _parse_header(lines)
    assert has_ns is False


def test_parse_header_no_includes(ct):
    """Parses header with no #include lines at all."""
    _parse_header = getattr(ct, "_parse_header")
    inc, _, _, _ = _parse_header([])
    assert not inc


def test_parse_header_non_using_stops_scan(ct):
    """Non-empty, non-using line stops the using-line scan."""
    _parse_header = getattr(ct, "_parse_header")
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "int x = 0;\n",
    ]
    _, using, _, _ = _parse_header(lines)
    assert using is None


def test_parse_header_blank_lines_before_using(ct):
    """Blank lines between includes and using-line are consumed."""
    _parse_header = getattr(ct, "_parse_header")
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "\n",
        "using namespace delta;\n",
    ]
    _, using, _, _ = _parse_header(lines)
    assert using is not None


# ---- _try_parse_preamble ---------------------------------------------------


def test_try_parse_preamble_brace_block(ct):
    """Parses a brace-delimited preamble item."""
    _try_parse_preamble = getattr(ct, "_try_parse_preamble")
    lines = ["struct Foo {\n", "};\n"]
    comments = []
    item, new_i = _try_parse_preamble(
        lines, 0, "struct Foo {", comments,
    )
    assert item is not None and new_i == 2


def test_try_parse_preamble_brace_block_with_comments(ct):
    """Preceding comments are prepended to brace-block items."""
    _try_parse_preamble = getattr(ct, "_try_parse_preamble")
    lines = ["struct Foo {\n", "};\n"]
    comments = ["// A comment"]
    item, _ = _try_parse_preamble(
        lines, 0, "struct Foo {", comments,
    )
    assert item.lines[0] == "// A comment"


def test_try_parse_preamble_semicolon(ct):
    """Parses a semicolon-terminated declaration."""
    _try_parse_preamble = getattr(ct, "_try_parse_preamble")
    lines = ["using T = int;\n"]
    comments = []
    item, new_i = _try_parse_preamble(
        lines, 0, "using T = int;", comments,
    )
    assert item is not None and new_i == 1


def test_try_parse_preamble_semicolon_with_comments(ct):
    """Preceding comments are prepended to semicolon declarations."""
    _try_parse_preamble = getattr(ct, "_try_parse_preamble")
    lines = ["using T = int;\n"]
    comments = ["// type alias"]
    item, _ = _try_parse_preamble(
        lines, 0, "using T = int;", comments,
    )
    assert item.lines[0] == "// type alias"


def test_try_parse_preamble_comment_accumulation(ct):
    """A line that is neither brace-block nor semicolon is a comment."""
    _try_parse_preamble = getattr(ct, "_try_parse_preamble")
    lines = ["something\n"]
    comments = []
    item, _ = _try_parse_preamble(
        lines, 0, "something", comments,
    )
    assert item is None and len(comments) == 1


def test_try_parse_preamble_unmatched_brace_falls_through(ct):
    """Unmatched brace falls through to semicolon / comment path."""
    _try_parse_preamble = getattr(ct, "_try_parse_preamble")
    lines = ["weird {\n"]
    comments = []
    item, _ = _try_parse_preamble(
        lines, 0, "weird {", comments,
    )
    assert item is None and len(comments) == 1


# ---- _parse_body -----------------------------------------------------------


def test_parse_body_extracts_test(ct):
    """Extracts TEST blocks from the body."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(Suite, MyTest) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_extracts_test_f(ct):
    """Extracts TEST_F blocks."""
    _parse_body = getattr(ct, "_parse_body")
    lines = ["TEST_F(Suite, MyTest) {\n", "}\n"]
    _, _, tests, _ = _parse_body(lines, 0)
    assert tests[0].suite_name == "Suite"


def test_parse_body_detects_namespace(ct):
    """Detects namespace { in body."""
    _parse_body = getattr(ct, "_parse_body")
    lines = ["namespace {\n", "TEST(S, T) {\n", "}\n"]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


def test_parse_body_skips_blank_and_closing(ct):
    """Blank lines and } // namespace are skipped."""
    _parse_body = getattr(ct, "_parse_body")
    lines = ["\n", "}  // namespace\n", "} // namespace\n"]
    g, _, tests, _ = _parse_body(lines, 0)
    assert not tests and not g


def test_parse_body_comments_attached(ct):
    """Comments before a TEST are attached as preceding_comments."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "// a comment\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests[0].preceding_comments) == 1


def test_parse_body_global_preamble(ct):
    """Preamble before first TEST goes to global_preamble."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "using T = int;\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    g_pre, _, _, _ = _parse_body(lines, 0)
    assert len(g_pre) == 1


def test_parse_body_section_preamble(ct):
    """Preamble after first TEST goes to section preamble."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "using U = float;\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    g_pre, _, tests, _ = _parse_body(lines, 0)
    assert not g_pre and len(tests) == 2


def test_parse_body_returns_section_preamble_count(ct):
    """Section preamble (helpers between tests) has one item."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "using U = float;\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    _, s_pre, _, _ = _parse_body(lines, 0)
    assert len(s_pre) == 1


def test_parse_body_returns_section_preamble_content(ct):
    """Section preamble item contains the using declaration."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "using U = float;\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    _, s_pre, _, _ = _parse_body(lines, 0)
    assert "using U = float;" in s_pre[0].lines[0]


def test_parse_body_section_preamble_brace_block_count(ct):
    """A brace-delimited helper between tests yields one preamble item."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "static int Helper() {\n",
        "  return 42;\n",
        "}\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    _, s_pre, _, _ = _parse_body(lines, 0)
    assert len(s_pre) == 1


def test_parse_body_section_preamble_brace_block_content(ct):
    """A brace-delimited helper preamble item contains the function signature."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "static int Helper() {\n",
        "  return 42;\n",
        "}\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    _, s_pre, _, _ = _parse_body(lines, 0)
    assert "static int Helper() {" in s_pre[0].lines[0]


def test_parse_body_non_test_non_semicolon(ct):
    """_parse_body handles lines returning None from _try_parse_preamble."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "something_odd\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_skips_named_namespace_opener(ct):
    """Named namespace opener is skipped, TEST inside is found."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta {\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_named_namespace_opener_sets_has_ns(ct):
    """Named namespace opener sets has_ns flag."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta {\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


def test_parse_body_skips_named_namespace_closer(ct):
    """Named namespace closer is skipped without error."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "TEST(S, T) {\n",
        "}\n",
        "}  // namespace delta\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_extracts_test_inside_named_namespace(ct):
    """TEST inside named + anonymous namespace wrappers is found."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta {\n",
        "namespace {\n",
        "\n",
        "TEST(NonLrmVpi, DefaultContextIsAvailable) {\n",
        "  EXPECT_TRUE(true);\n",
        "}\n",
        "\n",
        "}  // namespace\n",
        "}  // namespace delta\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_named_namespace_captures_test_name(ct):
    """TEST name is correctly captured inside named namespace."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta {\n",
        "namespace {\n",
        "\n",
        "TEST(NonLrmVpi, DefaultContextIsAvailable) {\n",
        "  EXPECT_TRUE(true);\n",
        "}\n",
        "\n",
        "}  // namespace\n",
        "}  // namespace delta\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert tests[0].test_name == "DefaultContextIsAvailable"


def test_parse_body_named_namespace_sets_has_ns(ct):
    """Named + anonymous namespace wrappers set has_ns."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta {\n",
        "namespace {\n",
        "\n",
        "TEST(NonLrmVpi, DefaultContextIsAvailable) {\n",
        "  EXPECT_TRUE(true);\n",
        "}\n",
        "\n",
        "}  // namespace\n",
        "}  // namespace delta\n",
    ]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


def test_parse_body_named_namespace_no_space_before_brace(ct):
    """Named namespace with no space before brace is handled."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta{\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_named_namespace_no_space_sets_has_ns(ct):
    """Named namespace without space before brace sets has_ns."""
    _parse_body = getattr(ct, "_parse_body")
    lines = [
        "namespace delta{\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


# ---- parse_file ------------------------------------------------------------


def test_parse_file_full(tmp_path, ct):
    """parse_file returns a ParsedFile with all components."""
    src = tmp_path / "test.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n"
        "\n"
        "namespace {\n"
        "\n"
        "TEST(S, T) {\n"
        "}\n"
        "\n"
        "}  // namespace\n",
        encoding="utf-8",
    )
    pf = ct.parse_file(src)
    assert len(pf.all_tests) == 1


def test_parse_file_body_namespace(tmp_path, ct):
    """parse_file detects namespace from body when not in header."""
    src = tmp_path / "test.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n"
        "\n"
        "TEST(S, T) {\n"
        "}\n",
        encoding="utf-8",
    )
    pf = ct.parse_file(src)
    assert pf.has_namespace_wrapper is False


_NAMED_NS_FILE = (
    "#include <gtest/gtest.h>\n"
    "\n"
    "#include \"simulation/vpi.h\"\n"
    "\n"
    "namespace delta {\n"
    "namespace {\n"
    "\n"
    "TEST(NonLrmVpi, DefaultContextIsAvailable) {\n"
    "  SetGlobalVpiContext(nullptr);\n"
    "  VpiContext &ctx = GetGlobalVpiContext();\n"
    "  (void)ctx;\n"
    "}\n"
    "\n"
    "}  // namespace\n"
    "}  // namespace delta\n"
)


def test_parse_file_named_namespace_finds_test(tmp_path, ct):
    """parse_file extracts the test from a named namespace file."""
    src = tmp_path / "test.cpp"
    src.write_text(_NAMED_NS_FILE, encoding="utf-8")
    pf = ct.parse_file(src)
    assert len(pf.all_tests) == 1


def test_parse_file_named_namespace_test_name(tmp_path, ct):
    """parse_file captures correct test name from named namespace file."""
    src = tmp_path / "test.cpp"
    src.write_text(_NAMED_NS_FILE, encoding="utf-8")
    pf = ct.parse_file(src)
    assert pf.all_tests[0].test_name == "DefaultContextIsAvailable"


def test_parse_file_named_namespace_has_ns(tmp_path, ct):
    """parse_file detects namespace wrapper in named namespace file."""
    src = tmp_path / "test.cpp"
    src.write_text(_NAMED_NS_FILE, encoding="utf-8")
    pf = ct.parse_file(src)
    assert pf.has_namespace_wrapper is True


# ---- multi-line TEST macro -------------------------------------------------


def test_parse_body_multiline_test_macro(ct):
    """_parse_body finds TEST macros split across two lines."""
    lines = [
        "TEST(MySuite,\n",
        "     MyTest) {\n",
        "  EXPECT_TRUE(true);\n",
        "}\n",
    ]
    parse_body = getattr(ct, "_parse_body")
    _, _, tests, _ = parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_multiline_test_name(ct):
    """_parse_body extracts the correct test name from multi-line macro."""
    lines = [
        "TEST(MySuite,\n",
        "     MyTest) {\n",
        "  EXPECT_TRUE(true);\n",
        "}\n",
    ]
    parse_body = getattr(ct, "_parse_body")
    _, _, tests, _ = parse_body(lines, 0)
    assert tests[0].test_name == "MyTest"


def test_parse_body_multiline_test_suite(ct):
    """_parse_body extracts the correct suite name from multi-line macro."""
    lines = [
        "TEST(MySuite,\n",
        "     MyTest) {\n",
        "  EXPECT_TRUE(true);\n",
        "}\n",
    ]
    parse_body = getattr(ct, "_parse_body")
    _, _, tests, _ = parse_body(lines, 0)
    assert tests[0].suite_name == "MySuite"
