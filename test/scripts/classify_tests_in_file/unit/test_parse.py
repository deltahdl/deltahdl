"""Unit tests for parsing functions in classify_tests_in_file."""

from pathlib import Path

import pytest

import classify_tests_in_file
from helpers import make_test_block as _tb

_update_brace_depth = getattr(classify_tests_in_file, "_update_brace_depth")
_parse_header = getattr(classify_tests_in_file, "_parse_header")
_try_parse_preamble = getattr(classify_tests_in_file, "_try_parse_preamble")
_parse_body = getattr(classify_tests_in_file, "_parse_body")


# ---- find_repo_root --------------------------------------------------------


def test_find_repo_root_exits_when_no_repo_root(tmp_path, monkeypatch):
    """find_repo_root exits when no test/CMakeLists.txt exists."""
    monkeypatch.setattr(Path, "cwd", staticmethod(lambda: tmp_path))
    with pytest.raises(SystemExit):
        classify_tests_in_file.find_repo_root()


def test_find_repo_root_returns_repo_root(tmp_path, monkeypatch):
    """find_repo_root returns the directory containing test/CMakeLists.txt."""
    (tmp_path / "test").mkdir()
    (tmp_path / "test" / "CMakeLists.txt").write_text("")
    child = tmp_path / "sub" / "deep"
    child.mkdir(parents=True)
    monkeypatch.setattr(Path, "cwd", staticmethod(lambda: child))
    assert classify_tests_in_file.find_repo_root() == tmp_path


# ---- _update_brace_depth ---------------------------------------------------


def test_update_brace_depth_open_brace_increments():
    """Opening brace increments depth."""
    d, _, _, found = _update_brace_depth("{", 0, False, False)
    assert d == 1 and not found


def test_update_brace_depth_close_brace_at_one_returns_found():
    """Closing brace at depth 1 returns found=True."""
    d, _, _, found = _update_brace_depth("}", 1, False, False)
    assert d == 0 and found


def test_update_brace_depth_close_brace_non_zero_no_found():
    """Closing brace when depth > 1 does not signal found."""
    d, _, _, found = _update_brace_depth("}", 2, False, False)
    assert d == 1 and not found


def test_update_brace_depth_ignores_braces_in_string():
    """Braces inside a string literal are ignored."""
    d, ins, _, _ = _update_brace_depth(
        '"{"', 0, False, False,
    )
    assert d == 0 and not ins


def test_update_brace_depth_escape_in_string():
    """Backslash inside a string skips the next character."""
    d, ins, _, _ = _update_brace_depth(
        r'"\""', 0, False, False,
    )
    assert d == 0 and not ins


def test_update_brace_depth_line_comment():
    """// comment causes remainder of line to be skipped."""
    d, _, _, _ = _update_brace_depth(
        "// {", 0, False, False,
    )
    assert d == 0


def test_update_brace_depth_block_comment_start():
    """/* starts a block comment."""
    _, _, bc, _ = _update_brace_depth(
        "/* {", 0, False, False,
    )
    assert bc is True


def test_update_brace_depth_block_comment_end():
    """*/ ends a block comment."""
    _, _, bc, _ = _update_brace_depth(
        "*/", 0, False, True,
    )
    assert bc is False


def test_update_brace_depth_stays_in_block_comment():
    """Non-closing chars inside block comment stay in comment."""
    _, _, bc, _ = _update_brace_depth(
        "x y z", 0, False, True,
    )
    assert bc is True


def test_update_brace_depth_star_no_slash():
    """A * not followed by / does not end a block comment."""
    _, _, bc, _ = _update_brace_depth(
        "*x", 0, False, True,
    )
    assert bc is True


def test_update_brace_depth_empty_line():
    """An empty line leaves state unchanged."""
    assert _update_brace_depth("", 0, False, False) == (
        0, False, False, False,
    )


# ---- extract_brace_block ---------------------------------------------------


def test_extract_brace_block_single_line():
    """Extracts a simple single-line brace block."""
    _, end = classify_tests_in_file.extract_brace_block(["{}\n"], 0)
    assert end == 0


def test_extract_brace_block_multi_line():
    """Extracts a multi-line brace block."""
    lines = ["{\n", "  x;\n", "}\n"]
    block, end = classify_tests_in_file.extract_brace_block(lines, 0)
    assert end == 2 and len(block) == 3


def test_extract_brace_block_unmatched():
    """Raises ValueError for unmatched braces."""
    with pytest.raises(ValueError, match="Unmatched brace"):
        classify_tests_in_file.extract_brace_block(["{\n"], 0)


# ---- is_section_header -----------------------------------------------------


def test_is_section_header_equals_banner():
    """Lines with 10+ '=' are section headers."""
    assert classify_tests_in_file.is_section_header("// ==========") is True


def test_is_section_header_dash_banner():
    """Lines with 10+ '-' are section headers."""
    assert classify_tests_in_file.is_section_header("// ----------") is True


def test_is_section_header_too_short():
    """Fewer than 10 repeated chars is not a header."""
    assert classify_tests_in_file.is_section_header("// ===") is False


def test_is_section_header_no_comment():
    """A line not starting with // is not a header."""
    assert classify_tests_in_file.is_section_header("==========") is False


def test_is_section_header_mixed():
    """A mixed =- line is not a header."""
    assert classify_tests_in_file.is_section_header("// ====------") is False


# ---- _parse_header ---------------------------------------------------------


def test_parse_header_full():
    """Parses includes, using-line, and namespace."""
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


def test_parse_header_no_using():
    """Parses header without a using-line."""
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "namespace {\n",
    ]
    _, using, _, _ = _parse_header(lines)
    assert using is None


def test_parse_header_no_namespace():
    """Parses header without namespace wrapper."""
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "TEST(S, T) {\n",
    ]
    _, _, has_ns, _ = _parse_header(lines)
    assert has_ns is False


def test_parse_header_no_includes():
    """Parses header with no #include lines at all."""
    inc, _, _, _ = _parse_header([])
    assert not inc


def test_parse_header_non_using_stops_scan():
    """Non-empty, non-using line stops the using-line scan."""
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "int x = 0;\n",
    ]
    _, using, _, _ = _parse_header(lines)
    assert using is None


def test_parse_header_blank_lines_before_using():
    """Blank lines between includes and using-line are consumed."""
    lines = [
        "#include <gtest/gtest.h>\n",
        "\n",
        "\n",
        "using namespace delta;\n",
    ]
    _, using, _, _ = _parse_header(lines)
    assert using is not None


# ---- _try_parse_preamble ---------------------------------------------------


def test_try_parse_preamble_brace_block():
    """Parses a brace-delimited preamble item."""
    lines = ["struct Foo {\n", "};\n"]
    comments = []
    item, new_i = _try_parse_preamble(
        lines, 0, "struct Foo {", comments,
    )
    assert item is not None and new_i == 2


def test_try_parse_preamble_brace_block_with_comments():
    """Preceding comments are prepended to brace-block items."""
    lines = ["struct Foo {\n", "};\n"]
    comments = ["// A comment"]
    item, _ = _try_parse_preamble(
        lines, 0, "struct Foo {", comments,
    )
    assert item.lines[0] == "// A comment"


def test_try_parse_preamble_semicolon():
    """Parses a semicolon-terminated declaration."""
    lines = ["using T = int;\n"]
    comments = []
    item, new_i = _try_parse_preamble(
        lines, 0, "using T = int;", comments,
    )
    assert item is not None and new_i == 1


def test_try_parse_preamble_semicolon_with_comments():
    """Preceding comments are prepended to semicolon declarations."""
    lines = ["using T = int;\n"]
    comments = ["// type alias"]
    item, _ = _try_parse_preamble(
        lines, 0, "using T = int;", comments,
    )
    assert item.lines[0] == "// type alias"


def test_try_parse_preamble_comment_accumulation():
    """A line that is neither brace-block nor semicolon is a comment."""
    lines = ["something\n"]
    comments = []
    item, _ = _try_parse_preamble(
        lines, 0, "something", comments,
    )
    assert item is None and len(comments) == 1


def test_try_parse_preamble_unmatched_brace_falls_through():
    """Unmatched brace falls through to semicolon / comment path."""
    lines = ["weird {\n"]
    comments = []
    item, _ = _try_parse_preamble(
        lines, 0, "weird {", comments,
    )
    assert item is None and len(comments) == 1


# ---- _parse_body -----------------------------------------------------------


def test_parse_body_extracts_test():
    """Extracts TEST blocks from the body."""
    lines = [
        "TEST(Suite, MyTest) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_extracts_test_f():
    """Extracts TEST_F blocks."""
    lines = ["TEST_F(Suite, MyTest) {\n", "}\n"]
    _, _, tests, _ = _parse_body(lines, 0)
    assert tests[0].suite_name == "Suite"


def test_parse_body_detects_namespace():
    """Detects namespace { in body."""
    lines = ["namespace {\n", "TEST(S, T) {\n", "}\n"]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


def test_parse_body_skips_blank_and_closing():
    """Blank lines and } // namespace are skipped."""
    lines = ["\n", "}  // namespace\n", "} // namespace\n"]
    g, _, tests, _ = _parse_body(lines, 0)
    assert not tests and not g


def test_parse_body_comments_attached():
    """Comments before a TEST are attached as preceding_comments."""
    lines = [
        "// a comment\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests[0].preceding_comments) == 1


def test_parse_body_global_preamble():
    """Preamble before first TEST goes to global_preamble."""
    lines = [
        "using T = int;\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    g_pre, _, _, _ = _parse_body(lines, 0)
    assert len(g_pre) == 1


def test_parse_body_section_preamble():
    """Preamble after first TEST goes to section preamble."""
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "using U = float;\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    g_pre, _, tests, _ = _parse_body(lines, 0)
    assert not g_pre and len(tests) == 2


def test_parse_body_returns_section_preamble():
    """Section preamble (helpers between tests) is returned."""
    lines = [
        "TEST(S, T1) {\n",
        "}\n",
        "using U = float;\n",
        "TEST(S, T2) {\n",
        "}\n",
    ]
    _, s_pre, _, _ = _parse_body(lines, 0)
    assert len(s_pre) == 1
    assert "using U = float;" in s_pre[0].lines[0]


def test_parse_body_section_preamble_brace_block():
    """A brace-delimited helper between tests is returned as section preamble."""
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
    assert "static int Helper() {" in s_pre[0].lines[0]


def test_parse_body_non_test_non_semicolon():
    """_parse_body handles lines returning None from _try_parse_preamble."""
    lines = [
        "something_odd\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_skips_named_namespace_opener():
    """Named namespace opener is skipped, TEST inside is found."""
    lines = [
        "namespace delta {\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_named_namespace_opener_sets_has_ns():
    """Named namespace opener sets has_ns flag."""
    lines = [
        "namespace delta {\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


def test_parse_body_skips_named_namespace_closer():
    """Named namespace closer is skipped without error."""
    lines = [
        "TEST(S, T) {\n",
        "}\n",
        "}  // namespace delta\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_extracts_test_inside_named_namespace():
    """TEST inside named + anonymous namespace wrappers is found."""
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


def test_parse_body_named_namespace_captures_test_name():
    """TEST name is correctly captured inside named namespace."""
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


def test_parse_body_named_namespace_sets_has_ns():
    """Named + anonymous namespace wrappers set has_ns."""
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


def test_parse_body_named_namespace_no_space_before_brace():
    """Named namespace with no space before brace is handled."""
    lines = [
        "namespace delta{\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, tests, _ = _parse_body(lines, 0)
    assert len(tests) == 1


def test_parse_body_named_namespace_no_space_sets_has_ns():
    """Named namespace without space before brace sets has_ns."""
    lines = [
        "namespace delta{\n",
        "TEST(S, T) {\n",
        "}\n",
    ]
    _, _, _, has_ns = _parse_body(lines, 0)
    assert has_ns is True


# ---- parse_file ------------------------------------------------------------


def test_parse_file_full(tmp_path):
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
    pf = classify_tests_in_file.parse_file(src)
    assert len(pf.all_tests) == 1


def test_parse_file_body_namespace(tmp_path):
    """parse_file detects namespace from body when not in header."""
    src = tmp_path / "test.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n"
        "\n"
        "TEST(S, T) {\n"
        "}\n",
        encoding="utf-8",
    )
    pf = classify_tests_in_file.parse_file(src)
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


def test_parse_file_named_namespace_finds_test(tmp_path):
    """parse_file extracts the test from a named namespace file."""
    src = tmp_path / "test.cpp"
    src.write_text(_NAMED_NS_FILE, encoding="utf-8")
    pf = classify_tests_in_file.parse_file(src)
    assert len(pf.all_tests) == 1


def test_parse_file_named_namespace_test_name(tmp_path):
    """parse_file captures correct test name from named namespace file."""
    src = tmp_path / "test.cpp"
    src.write_text(_NAMED_NS_FILE, encoding="utf-8")
    pf = classify_tests_in_file.parse_file(src)
    assert pf.all_tests[0].test_name == "DefaultContextIsAvailable"


def test_parse_file_named_namespace_has_ns(tmp_path):
    """parse_file detects namespace wrapper in named namespace file."""
    src = tmp_path / "test.cpp"
    src.write_text(_NAMED_NS_FILE, encoding="utf-8")
    pf = classify_tests_in_file.parse_file(src)
    assert pf.has_namespace_wrapper is True
