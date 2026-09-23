from lib.python import run_tests_common


def test_lists_every_subclause_in_the_order_written() -> None:
    stderr = (
        "a.sv:1:1: error: enum has an x assignment (§6.19)\n"
        "a.sv:2:1: error: bad randomize() call (§16.12.17)\n"
    )
    assert run_tests_common.reported_subclauses(stderr) == ["6.19", "16.12.17"]


def test_lists_nothing_when_no_diagnostic_names_a_subclause() -> None:
    stderr = "a.sv:1:1: error: cannot open include file 'x.svh'\n"
    assert run_tests_common.reported_subclauses(stderr) == []


def test_a_clause_contains_itself() -> None:
    assert run_tests_common.subclause_is_within("6.19", "6.19") is True


def test_a_clause_contains_a_deeper_subclause() -> None:
    assert run_tests_common.subclause_is_within("16.12.17", "16.12") is True


def test_a_clause_does_not_contain_a_longer_number() -> None:
    assert run_tests_common.subclause_is_within("16.121", "16.12") is False


def test_a_clause_does_not_contain_the_clause_above_it() -> None:
    assert run_tests_common.subclause_is_within("16", "16.12") is False
