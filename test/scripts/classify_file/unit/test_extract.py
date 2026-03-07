"""Unit tests for test name extraction in classify_file."""


# ---- extract_test_names ----------------------------------------------------


def test_extract_test_names_single(tmp_path, cf, cf_helpers):
    """Extracts a single TEST name."""
    f = cf_helpers.make_test_file(tmp_path, "TEST(S, Alpha) {\n}\n")
    assert cf.extract_test_names(f) == ["Alpha"]


def test_extract_test_names_multiple(tmp_path, cf, cf_helpers):
    """Extracts multiple TEST names in order."""
    body = "TEST(S, Alpha) {\n}\nTEST(S, Beta) {\n}\n"
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_test_names(f) == ["Alpha", "Beta"]


def test_extract_test_names_test_f(tmp_path, cf, cf_helpers):
    """Extracts TEST_F names."""
    f = cf_helpers.make_test_file(tmp_path, "TEST_F(Suite, Gamma) {\n}\n")
    assert cf.extract_test_names(f) == ["Gamma"]


def test_extract_test_names_test_p(tmp_path, cf, cf_helpers):
    """Extracts TEST_P names."""
    f = cf_helpers.make_test_file(tmp_path, "TEST_P(Suite, Delta) {\n}\n")
    assert cf.extract_test_names(f) == ["Delta"]


def test_extract_test_names_empty_file(tmp_path, cf, cf_helpers):
    """Returns empty list for file with no tests."""
    f = cf_helpers.make_test_file(tmp_path, "#include <gtest/gtest.h>\n")
    assert cf.extract_test_names(f) == []


def test_extract_test_names_preserves_order(tmp_path, cf, cf_helpers):
    """Returns names in file order, not sorted."""
    body = "TEST(S, Zulu) {\n}\nTEST(S, Alpha) {\n}\n"
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_test_names(f) == ["Zulu", "Alpha"]


def test_extract_test_names_with_whitespace(tmp_path, cf, cf_helpers):
    """Handles whitespace around test macro arguments."""
    f = cf_helpers.make_test_file(tmp_path, "  TEST( S , Name ) {\n}\n")
    assert cf.extract_test_names(f) == ["Name"]


def test_extract_test_names_ignores_comments(tmp_path, cf, cf_helpers):
    """Does not extract names from commented-out TEST lines."""
    f = cf_helpers.make_test_file(tmp_path, "// TEST(S, Fake) {\n}\n")
    assert cf.extract_test_names(f) == []


def test_extract_test_names_mixed(tmp_path, cf, cf_helpers):
    """Extracts from mixed TEST/TEST_F/TEST_P."""
    body = (
        "TEST(S, A) {\n}\n"
        "TEST_F(S, B) {\n}\n"
        "TEST_P(S, C) {\n}\n"
    )
    f = cf_helpers.make_test_file(tmp_path, body)
    assert cf.extract_test_names(f) == ["A", "B", "C"]
