from lib.python.subclause import (
    build_hierarchy,
)


def test_build_hierarchy_numeric_depth_1() -> None:
    assert build_hierarchy("4")["clause_number"] == "4"


def test_build_hierarchy_numeric_no_ancestors() -> None:
    assert build_hierarchy("4.1")["ancestors"] == []


def test_build_hierarchy_numeric_ancestors() -> None:
    assert build_hierarchy("6.24.1")["ancestors"] == ["6.24"]


def test_build_hierarchy_annex_letter() -> None:
    assert build_hierarchy("B")["letter"] == "B"


def test_build_hierarchy_annex_is_annex() -> None:
    assert build_hierarchy("A.8")["is_annex"] is True


def test_build_hierarchy_numeric_not_annex() -> None:
    assert build_hierarchy("4")["is_annex"] is False


def test_build_hierarchy_annex_ancestors() -> None:
    assert build_hierarchy("A.8.1")["ancestors"] == ["A.8"]
