from lib.python.lrm import identifier_kind


TOC = {
    "11": (250, 306),
    "11.4": (272, 292),
    "11.4.11": (286, 286),
    "41": (1171, 1172),
    "A": (1173, 1219),
    "A.10": (1217, 1219),
    "B": (1220, 1221),
}


def test_bare_number_is_a_clause() -> None:
    assert identifier_kind("41", TOC) == "clause"


def test_bare_letter_is_an_annex() -> None:
    assert identifier_kind("B", TOC) == "annex"


def test_numbered_division_of_an_annex_is_a_subclause() -> None:
    assert identifier_kind("A.10", TOC) == "subclause"


def test_numbered_division_of_a_clause_is_a_subclause() -> None:
    assert identifier_kind("11.4.11", TOC) == "subclause"


def test_identifier_outside_the_toc_has_no_kind() -> None:
    assert identifier_kind("99", TOC) is None
