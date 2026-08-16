"""Tests for pairing a diagnostic message with the subclause of its call."""

from assert_subclause_citations import message_subclause_pairs


def test_it_pairs_a_message_with_the_subclause_beside_it() -> None:
    """The pair is what says which rule a sentence a user reads enforces."""
    text = 'diag.Error(loc, "bad thing", Subclause("5.2"));'
    assert message_subclause_pairs(text) == {("bad thing", "5.2")}


def test_adjacent_literals_make_one_message() -> None:
    """C++ joins them, so a sentence too long for one line is written twice.

    Reading one literal would give a message nobody is ever shown, which is
    how a stale assertion in test/src/unit/test_elaborator_annex_g_07.cpp hid
    from a search during #3058.
    """
    text = 'diag.Error(loc, "one long " "sentence", Subclause("5.2"));'
    assert message_subclause_pairs(text) == {("one long sentence", "5.2")}


def test_the_subclause_is_not_part_of_the_message() -> None:
    """Its digits are a citation, not a word of the sentence."""
    text = 'diag.Error(loc, "bad", Subclause("11.4.14"));'
    assert message_subclause_pairs(text) == {("bad", "11.4.14")}


def test_a_warning_is_paired_as_an_error_is() -> None:
    """Some rules are enforced with a warning, and they cite a clause too."""
    text = 'diag.Warning(loc, "odd", Subclause("23.3.2"));'
    assert message_subclause_pairs(text) == {("odd", "23.3.2")}


def test_a_comment_naming_a_subclause_pairs_with_nothing() -> None:
    """Citations are read out of code, which strip_cpp_comments settles."""
    text = '/* diag.Error(loc, "bad", Subclause("5.2")); */'
    assert not message_subclause_pairs(text)


def test_a_call_choosing_between_two_subclauses_is_left_out() -> None:
    """One site picking the clause its construct answers to is not the fault.

    src/parser/parser_items.cpp cites §13.3 for a task and §13.4 for a
    function from a single report, and the fault this pairing is for is two
    sites disagreeing.
    """
    text = ('diag.Error(loc, "qualifier misplaced",'
            ' is_task ? Subclause("13.3") : Subclause("13.4"));')
    assert not message_subclause_pairs(text)


def test_a_call_with_no_message_literal_is_left_out() -> None:
    """A message a helper built holds no sentence for this to read."""
    text = 'diag.Error(loc, BuildMessage(kind), Subclause("6.6.7"));'
    assert not message_subclause_pairs(text)
