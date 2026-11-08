from pathlib import Path

import pytest

from assert_subclause_citations import known_subclauses


def test_each_form_of_identifier_is_returned(tmp_path: Path) -> None:
    path = tmp_path / "clauses.txt"
    path.write_text("1\n6.20.3\nA\nA.1.10\n")
    assert known_subclauses(path) == {"1", "6.20.3", "A", "A.1.10"}


@pytest.mark.parametrize(
    "line",
    [
        "# note",
        "  # note",
        "#",
        "",
        "   ",
        " 6.1",
        "\t6.1",
        "6.1 ",
        "6.1 # note",
        "1 2",
        "6.20.",
        ".1",
        "6..1",
        "a.1",
        "AB.1",
        "A1",
        "1.A",
    ],
)
def test_a_line_that_is_not_an_identifier_is_reported(
    tmp_path: Path, line: str
) -> None:
    path = tmp_path / "clauses.txt"
    path.write_text(f"1\n{line}\n2\n")
    with pytest.raises(ValueError) as raised:
        known_subclauses(path)
    assert str(raised.value) == (
        f"{path}:2: {line!r} is not a clause identifier"
    )


def test_the_committed_list_holds_a_clause_the_standard_defines() -> None:
    assert "11.4.14" in known_subclauses()


def test_the_committed_list_lacks_a_number_with_no_clause() -> None:
    assert "6.20.3.1" not in known_subclauses()
