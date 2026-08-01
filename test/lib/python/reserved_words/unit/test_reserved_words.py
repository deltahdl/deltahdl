"""Tests for the reading that finds a reserved word used as a name.

The sources below put the SystemVerilog inside string literals and ordinary C++
around them, because telling those apart is most of what the reading does: the
same word is a fault in one and unremarkable in the other.
"""

from lib.python.reserved_words import (
    RESERVED,
    declarations_in,
    literals_of,
    reserved_declarations,
)

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

LIFETIME_AND_TYPE = (
    '"module automatic one_cell;\\n"\n'
    '"  wire logic earlier;\\n"\n'
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
    """A design declaring `cell` and `before` declares nothing at all."""
    assert reserved_declarations(DECLARES_A_KEYWORD) == [
        "module cell", "wire before"
    ]


def test_a_reserved_word_in_the_c_plus_plus_is_not_reported() -> None:
    """`int before = 0;` is C++ and is nobody's design."""
    assert not reserved_declarations(DECLARES_NAMES_OF_ITS_OWN)


def test_what_the_standard_allows_between_the_two_is_not_reported() -> None:
    """A lifetime, a data type and `interface class` are not names."""
    assert not reserved_declarations(LIFETIME_AND_TYPE)


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
