"""Tests for reading the arguments of a diagnostic call out of C++ text."""

from assert_subclause_citations import diagnostic_call_arguments


def test_it_reads_the_arguments_of_a_report() -> None:
    """The text between the call's parentheses comes back whole."""
    text = 'diag.Error(loc, "no", Subclause("5.2"));'
    assert diagnostic_call_arguments(text) == ['loc, "no", Subclause("5.2")']


def test_a_nested_call_does_not_end_the_one_holding_it() -> None:
    """std::format assembles most messages, so its parentheses come back."""
    text = 'diag.Error(loc, std::format("a {}", n), Subclause("5.2"));'
    assert diagnostic_call_arguments(text) == [
        'loc, std::format("a {}", n), Subclause("5.2")'
    ]


def test_a_parenthesis_in_a_string_literal_closes_nothing() -> None:
    """src/parser/parser_verify.cpp reports missing ')' in covergroup item."""
    text = """diag.Error(loc, "missing ')' here", Subclause("19.3"));"""
    assert diagnostic_call_arguments(text) == [
        """loc, "missing ')' here", Subclause("19.3")"""
    ]


def test_a_parenthesis_in_a_character_literal_closes_nothing() -> None:
    """A lone ')' written as a char is a value and not punctuation."""
    text = """diag.Error(loc, Spelling(')'), Subclause("19.3"));"""
    assert diagnostic_call_arguments(text) == [
        """loc, Spelling(')'), Subclause("19.3")"""
    ]


def test_a_call_nothing_closes_is_read_to_the_end() -> None:
    """A source that does not compile still answers rather than raising."""
    assert diagnostic_call_arguments("diag.Error(loc, ") == ["loc, "]
