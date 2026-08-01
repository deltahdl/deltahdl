"""Tests for the reading that finds a reserved word used as a name.

The sources below put the SystemVerilog inside string literals and ordinary C++
around them, because telling those apart is most of what the reading does: the
same word is a fault in one and unremarkable in the other.
"""

from lib.python.reserved_words import (
    RESERVED,
    chooses_its_own_keywords,
    declarations_in,
    literals_of,
    reserved_declarations,
)

UNDER_AN_EARLIER_TABLE = (
    '"`begin_keywords \\"1364-2001\\"\\n"\n'
    '"module bit;\\n"\n'
    '"`end_keywords\\n"'
)

A_NET = '"wire before;\\n"'

QUOTES_THE_STANDARD = (
    '// "Each module instance ... has an initialization RNG." A comment is\n'
    '// prose about SystemVerilog rather than SystemVerilog.\n'
)

A_LIST_OF_KEYWORDS = 'auto tokens = Lex("module primitive program interface");'

DECLARES_A_KEYWORD = '''
TEST(SinglePassPrecompile, ChangedDescriptionIsCompiledAgain) {
  int before = 0;
  auto src = tmp.Write("src/cell.v",
                       "module cell;\\n"
                       "  wire before;\\n"
                       "endmodule\\n");
}
'''

DECLARES_NAMES_OF_ITS_OWN = '''
TEST(SinglePassPrecompile, ChangedDescriptionIsCompiledAgain) {
  int before = 0;
  auto src = tmp.Write("src/cell.v",
                       "module one_cell;\\n"
                       "  wire earlier;\\n"
                       "endmodule\\n");
}
'''

LIFETIME_AND_INTERFACE_CLASS = (
    '"module automatic one_cell;\\n"\n'
    '"interface class shape;\\n"'
)

LIFETIME_AHEAD_OF_A_KEYWORD = '"module static cell;\\n"'


def test_a_literal_gives_up_what_it_holds() -> None:
    """The SystemVerilog a test hands over is what stands in its literals."""
    assert literals_of('f("module one_cell;\\n", x)') == ["module one_cell;\\n"]


def test_a_source_with_no_literal_holds_no_systemverilog() -> None:
    """C++ that hands over nothing has nothing for the reading to read."""
    assert not literals_of("int before = 0;")


def test_a_declaration_is_the_keyword_and_the_name_after_it() -> None:
    """What follows the keyword is the name the source is declaring."""
    assert declarations_in("module one_cell;") == [("module", "one_cell")]


def test_a_lifetime_between_the_two_is_not_the_name() -> None:
    """§23.2 lets a lifetime stand there, so the name is the word after it."""
    assert declarations_in("module automatic one_cell;") == [
        ("module", "one_cell")
    ]


def test_a_reserved_name_in_a_literal_is_reported() -> None:
    """A design element called `cell` is not a design element at all."""
    assert reserved_declarations(DECLARES_A_KEYWORD) == ["module cell"]


def test_a_reserved_word_in_the_c_plus_plus_is_not_reported() -> None:
    """`int before = 0;` is C++ and is nobody's design."""
    assert not reserved_declarations(DECLARES_NAMES_OF_ITS_OWN)


def test_what_the_standard_allows_between_the_two_is_not_reported() -> None:
    """A lifetime and the `class` of an interface class are not names."""
    assert not reserved_declarations(LIFETIME_AND_INTERFACE_CLASS)


def test_a_reserved_name_behind_a_lifetime_is_still_reported() -> None:
    """Passing over the lifetime means reading on, not giving up."""
    assert reserved_declarations(LIFETIME_AHEAD_OF_A_KEYWORD) == [
        "module cell"
    ]


def test_the_word_this_repository_first_tripped_over_is_reserved() -> None:
    """`cell` is Table B.1's, which is why `module cell;` never parsed."""
    assert "cell" in RESERVED


def test_a_word_the_standard_leaves_alone_is_not_reserved() -> None:
    """`after` is not in Table B.1, though `before` is."""
    assert "after" not in RESERVED


def test_a_source_naming_a_version_specifier_picks_its_own_table() -> None:
    """§22.14 puts the reserved set under the source's own control."""
    assert chooses_its_own_keywords(UNDER_AN_EARLIER_TABLE)


def test_a_source_naming_no_specifier_is_held_to_table_b_1() -> None:
    """Without one, the words this annex reserves are the ones in force."""
    assert chooses_its_own_keywords(DECLARES_A_KEYWORD) is False


def test_a_name_reserved_only_by_a_later_table_is_not_reported() -> None:
    """`module bit;` is a declaration under 1364-2001 and a test may say so."""
    assert not reserved_declarations(UNDER_AN_EARLIER_TABLE)


def test_a_net_declaration_is_outside_what_this_reads() -> None:
    """§6.7 lets any data type follow `wire`, so the next word need not be one."""
    assert not reserved_declarations(A_NET)


def test_a_comment_quoting_the_standard_is_not_read_as_a_design() -> None:
    """The quotation marks in a comment open prose, not a source."""
    assert not reserved_declarations(QUOTES_THE_STANDARD)


def test_two_keywords_in_a_row_are_not_a_declaration() -> None:
    """A lexer handed a list of words is handed no header to continue."""
    assert not reserved_declarations(A_LIST_OF_KEYWORDS)
