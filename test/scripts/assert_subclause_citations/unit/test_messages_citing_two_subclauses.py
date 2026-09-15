from collections.abc import Callable, Mapping
from pathlib import Path

from assert_subclause_citations import messages_citing_two_subclauses

TreeBuilder = Callable[[Mapping[str, str]], Path]


def test_two_sites_sharing_a_message_are_reported_with_both_clauses(
    make_tree: TreeBuilder,
) -> None:
    root = make_tree({
        "one.cpp": 'diag.Error(loc, "shared", Subclause("6.21"));',
        "two.cpp": 'diag.Error(loc, "shared", Subclause("13.3.2"));',
    })
    assert messages_citing_two_subclauses(root) == {
        "shared": {"6.21", "13.3.2"}
    }


def test_two_sites_agreeing_on_the_clause_are_not_reported(
    make_tree: TreeBuilder,
) -> None:
    root = make_tree({
        "one.cpp": 'diag.Error(loc, "shared", Subclause("6.21"));',
        "two.cpp": 'diag.Error(loc, "shared", Subclause("6.21"));',
    })
    assert not messages_citing_two_subclauses(root)


def test_two_messages_under_one_clause_are_not_reported(
    make_tree: TreeBuilder,
) -> None:
    root = make_tree({
        "one.cpp": ('diag.Error(loc, "first", Subclause("6.21"));'
                    'diag.Error(loc, "second", Subclause("6.21"));'),
    })
    assert not messages_citing_two_subclauses(root)


def test_a_file_that_is_not_c_plus_plus_is_not_read(
    make_tree: TreeBuilder,
) -> None:
    root = make_tree({
        "one.cpp": 'diag.Error(loc, "shared", Subclause("6.21"));',
        "notes.txt": 'diag.Error(loc, "shared", Subclause("13.3.2"));',
    })
    assert not messages_citing_two_subclauses(root)


def test_a_header_is_read_as_a_source_is(make_tree: TreeBuilder) -> None:
    both = 'diag.Warning(loc, "in a header", Subclause("{}"));'
    root = make_tree({
        "sub/a.h": both.format("30.4.1"),
        "sub/b.h": both.format("31.2"),
    })
    assert messages_citing_two_subclauses(root)["in a header"] == {
        "30.4.1", "31.2",
    }
