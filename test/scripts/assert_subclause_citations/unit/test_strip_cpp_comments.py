from assert_subclause_citations import strip_cpp_comments


def test_a_line_comment_becomes_one_space() -> None:
    assert strip_cpp_comments("a;// gone\nb;") == "a; \nb;"


def test_a_line_comment_ending_the_text_becomes_one_space() -> None:
    assert strip_cpp_comments("a;// gone") == "a; "


def test_a_block_comment_becomes_one_space() -> None:
    assert strip_cpp_comments("a;/* gone */b;") == "a; b;"


def test_an_unterminated_block_comment_becomes_one_space() -> None:
    assert strip_cpp_comments("a;/* gone") == "a; "


def test_two_slashes_inside_a_string_literal_open_no_comment() -> None:
    assert strip_cpp_comments('f("a//b");') == 'f("a//b");'


def test_an_escaped_quote_does_not_close_a_string_literal() -> None:
    source = 'f("a\\"//b");'
    assert strip_cpp_comments(source) == source


def test_an_unterminated_string_literal_runs_to_the_end() -> None:
    source = 'f("a//b'
    assert strip_cpp_comments(source) == source
