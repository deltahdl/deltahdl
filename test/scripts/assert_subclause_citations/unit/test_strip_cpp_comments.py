"""Tests for strip_cpp_comments in assert_subclause_citations."""

from assert_subclause_citations import strip_cpp_comments


def test_a_line_comment_becomes_one_space() -> None:
    """A // comment is replaced, and the newline that ends it is kept."""
    assert strip_cpp_comments("a;// gone\nb;") == "a; \nb;"


def test_a_line_comment_ending_the_text_becomes_one_space() -> None:
    """A // comment that no newline ends runs to the end of the text."""
    assert strip_cpp_comments("a;// gone") == "a; "


def test_a_block_comment_becomes_one_space() -> None:
    """A /* */ comment is replaced by a space and not deleted, so the code
    on either side of it is not joined into a token nobody wrote."""
    assert strip_cpp_comments("a;/* gone */b;") == "a; b;"


def test_an_unterminated_block_comment_becomes_one_space() -> None:
    """A /* that nothing closes runs to the end of the text."""
    assert strip_cpp_comments("a;/* gone") == "a; "


def test_two_slashes_inside_a_string_literal_open_no_comment() -> None:
    """A string literal is copied out whole, // and all."""
    assert strip_cpp_comments('f("a//b");') == 'f("a//b");'


def test_an_escaped_quote_does_not_close_a_string_literal() -> None:
    r"""A \" inside a string literal is two characters and not its end.

    The // after it is still inside the literal, so a scan that took the
    escaped quote for the closing one would delete the rest of the line.
    """
    source = 'f("a\\"//b");'
    assert strip_cpp_comments(source) == source


def test_an_unterminated_string_literal_runs_to_the_end() -> None:
    """A string literal that no quote closes is copied to the end."""
    source = 'f("a//b'
    assert strip_cpp_comments(source) == source
