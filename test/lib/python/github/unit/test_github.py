from lib.python.github import (
    format_subclause_label,
    issue_title_for,
)


def test_format_subclause_label_numeric() -> None:
    assert format_subclause_label("3.14.1") == "§3.14.1"


def test_format_subclause_label_annex() -> None:
    assert format_subclause_label("A.1.1") == "A.1.1"


def test_issue_title_for_names_the_subclause_it_satisfies() -> None:
    assert issue_title_for("18.16") == "Satisfy IEEE 1800-2023 §18.16"
