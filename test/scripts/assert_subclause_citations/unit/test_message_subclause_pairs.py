from assert_subclause_citations import message_subclause_pairs


def test_it_pairs_a_message_with_the_subclause_beside_it() -> None:
    text = 'diag.Error(loc, "bad thing", Subclause("5.2"));'
    assert message_subclause_pairs(text) == {("bad thing", "5.2")}


def test_adjacent_literals_make_one_message() -> None:
    text = 'diag.Error(loc, "one long " "sentence", Subclause("5.2"));'
    assert message_subclause_pairs(text) == {("one long sentence", "5.2")}


def test_the_subclause_is_not_part_of_the_message() -> None:
    text = 'diag.Error(loc, "bad", Subclause("11.4.14"));'
    assert message_subclause_pairs(text) == {("bad", "11.4.14")}


def test_a_warning_is_paired_as_an_error_is() -> None:
    text = 'diag.Warning(loc, "odd", Subclause("23.3.2"));'
    assert message_subclause_pairs(text) == {("odd", "23.3.2")}


def test_a_comment_naming_a_subclause_pairs_with_nothing() -> None:
    text = '/* diag.Error(loc, "bad", Subclause("5.2")); */'
    assert not message_subclause_pairs(text)


def test_a_call_choosing_between_two_subclauses_is_left_out() -> None:
    text = ('diag.Error(loc, "qualifier misplaced",'
            ' is_task ? Subclause("13.3") : Subclause("13.4"));')
    assert not message_subclause_pairs(text)


def test_a_call_with_no_message_literal_is_left_out() -> None:
    text = 'diag.Error(loc, BuildMessage(kind), Subclause("6.6.7"));'
    assert not message_subclause_pairs(text)
