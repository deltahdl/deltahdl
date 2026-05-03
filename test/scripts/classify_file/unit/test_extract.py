"""Unit tests for test extraction in classify_file."""

from pathlib import Path
from types import ModuleType


# ---- extract_tests ---------------------------------------------------------


def test_extract_tests_single(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Extracts a single TEST as (suite, name) tuple."""
    f = cf_helpers.make_test_file(tmp_path, "TEST(S, Alpha) {\n}\n")
    assert cf.extract_tests(f) == [("S", "Alpha")]


def test_extract_tests_multiple(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Extracts multiple TEST tuples in order."""
    body = "TEST(S, Alpha) {\n}\nTEST(S, Beta) {\n}\n"
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_tests(f) == [("S", "Alpha"), ("S", "Beta")]


def test_extract_tests_test_f(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Extracts TEST_F tuples."""
    f = cf_helpers.make_test_file(tmp_path, "TEST_F(Suite, Gamma) {\n}\n")
    assert cf.extract_tests(f) == [("Suite", "Gamma")]


def test_extract_tests_test_p(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Extracts TEST_P tuples."""
    f = cf_helpers.make_test_file(tmp_path, "TEST_P(Suite, Delta) {\n}\n")
    assert cf.extract_tests(f) == [("Suite", "Delta")]


def test_extract_tests_empty_file(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Returns empty list for file with no tests."""
    f = cf_helpers.make_test_file(tmp_path, "#include <gtest/gtest.h>\n")
    assert cf.extract_tests(f) == []


def test_extract_tests_preserves_order(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Returns tuples in file order, not sorted."""
    body = "TEST(S, Zulu) {\n}\nTEST(S, Alpha) {\n}\n"
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_tests(f) == [("S", "Zulu"), ("S", "Alpha")]


def test_extract_tests_with_whitespace(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Handles whitespace around test macro arguments."""
    f = cf_helpers.make_test_file(tmp_path, "  TEST( S , Name ) {\n}\n")
    assert cf.extract_tests(f) == [("S", "Name")]


def test_extract_tests_ignores_comments(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Does not extract tuples from commented-out TEST lines."""
    f = cf_helpers.make_test_file(tmp_path, "// TEST(S, Fake) {\n}\n")
    assert cf.extract_tests(f) == []


def test_extract_tests_mixed(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Extracts from mixed TEST/TEST_F/TEST_P."""
    body = (
        "TEST(S, A) {\n}\n"
        "TEST_F(S, B) {\n}\n"
        "TEST_P(S, C) {\n}\n"
    )
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_tests(f) == [("S", "A"), ("S", "B"), ("S", "C")]


def test_extract_tests_different_suites(
        tmp_path: Path, cf: ModuleType, cf_helpers: ModuleType) -> None:
    """Extracts tests with different suite names."""
    body = "TEST(Parser, A) {\n}\nTEST(Lexer, B) {\n}\n"
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_tests(f) == [("Parser", "A"), ("Lexer", "B")]
