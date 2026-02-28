"""Unit tests for test name extraction in classify_file."""

import classify_file

from helpers import make_test_file


# ---- extract_test_names ----------------------------------------------------


def test_extract_test_names_single(tmp_path):
    """Extracts a single TEST name."""
    f = make_test_file(tmp_path, "TEST(S, Alpha) {\n}\n")
    assert classify_file.extract_test_names(f) == ["Alpha"]


def test_extract_test_names_multiple(tmp_path):
    """Extracts multiple TEST names in order."""
    body = "TEST(S, Alpha) {\n}\nTEST(S, Beta) {\n}\n"
    f = make_test_file(tmp_path, body)
    assert classify_file.extract_test_names(f) == ["Alpha", "Beta"]


def test_extract_test_names_test_f(tmp_path):
    """Extracts TEST_F names."""
    f = make_test_file(tmp_path, "TEST_F(Suite, Gamma) {\n}\n")
    assert classify_file.extract_test_names(f) == ["Gamma"]


def test_extract_test_names_test_p(tmp_path):
    """Extracts TEST_P names."""
    f = make_test_file(tmp_path, "TEST_P(Suite, Delta) {\n}\n")
    assert classify_file.extract_test_names(f) == ["Delta"]


def test_extract_test_names_empty_file(tmp_path):
    """Returns empty list for file with no tests."""
    f = make_test_file(tmp_path, "#include <gtest/gtest.h>\n")
    assert classify_file.extract_test_names(f) == []


def test_extract_test_names_preserves_order(tmp_path):
    """Returns names in file order, not sorted."""
    body = "TEST(S, Zulu) {\n}\nTEST(S, Alpha) {\n}\n"
    f = make_test_file(tmp_path, body)
    assert classify_file.extract_test_names(f) == ["Zulu", "Alpha"]


def test_extract_test_names_with_whitespace(tmp_path):
    """Handles whitespace around test macro arguments."""
    f = make_test_file(tmp_path, "  TEST( S , Name ) {\n}\n")
    assert classify_file.extract_test_names(f) == ["Name"]


def test_extract_test_names_ignores_comments(tmp_path):
    """Does not extract names from commented-out TEST lines."""
    f = make_test_file(tmp_path, "// TEST(S, Fake) {\n}\n")
    assert classify_file.extract_test_names(f) == []


def test_extract_test_names_mixed(tmp_path):
    """Extracts from mixed TEST/TEST_F/TEST_P."""
    body = (
        "TEST(S, A) {\n}\n"
        "TEST_F(S, B) {\n}\n"
        "TEST_P(S, C) {\n}\n"
    )
    f = make_test_file(tmp_path, body)
    assert classify_file.extract_test_names(f) == ["A", "B", "C"]
