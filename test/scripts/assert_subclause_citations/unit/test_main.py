"""Tests for main and for running assert_subclause_citations as a module."""

import runpy
from collections.abc import Callable, Mapping
from pathlib import Path

import pytest

from assert_subclause_citations import main

TreeBuilder = Callable[[Mapping[str, str]], Path]


def test_a_tree_citing_only_real_clauses_answers_zero(
    make_tree: TreeBuilder,
) -> None:
    """§11.4.14 is a clause of IEEE 1800-2023, so the run passes."""
    root = make_tree({"good.cpp": 'Subclause("11.4.14")'})
    assert main(root) == 0


def test_a_tree_citing_a_number_with_no_clause_answers_one(
    make_tree: TreeBuilder,
) -> None:
    """6.20.3.1 names no clause, so the run answers a failing status."""
    root = make_tree({"bad.cpp": 'Subclause("6.20.3.1")'})
    assert main(root) == 1


def test_the_report_names_the_file_the_bad_citation_is_in(
    make_tree: TreeBuilder, capsys: pytest.CaptureFixture[str],
) -> None:
    """The annotation carries the path, so a red run says what to open."""
    root = make_tree({"bad.cpp": 'Subclause("6.20.3.1")'})
    main(root)
    assert f"::error file={root / 'bad.cpp'}::" in capsys.readouterr().out


def test_the_report_names_the_citation_that_has_no_clause(
    make_tree: TreeBuilder, capsys: pytest.CaptureFixture[str],
) -> None:
    """The annotation carries the number cited, and not only the file."""
    main(make_tree({"nowhere.cpp": 'Subclause("6.20.3.1")'}))
    assert "cites 6.20.3.1" in capsys.readouterr().out


def test_a_tree_reporting_one_message_under_two_clauses_answers_one(
    make_tree: TreeBuilder,
) -> None:
    """Both clauses exist, so only the second check can fail this run."""
    root = make_tree({
        "one.cpp": 'diag.Error(loc, "shared", Subclause("11.4.14"));',
        "two.cpp": 'diag.Error(loc, "shared", Subclause("A.10"));',
    })
    assert main(root) == 1


def test_the_report_quotes_the_message_and_names_both_clauses(
    make_tree: TreeBuilder, capsys: pytest.CaptureFixture[str],
) -> None:
    """Its wording differs from the invalid-citation one, which is the point.

    The two faults are fixed differently -- one by correcting a citation, the
    other by telling two rules apart in the sentence -- so a reader of a red
    log should not have to work out which one fired.
    """
    main(make_tree({
        "one.cpp": 'diag.Error(loc, "shared", Subclause("11.4.14"));',
        "two.cpp": 'diag.Error(loc, "shared", Subclause("A.10"));',
    }))
    assert '"shared" is reported under §11.4.14, §A.10' in capsys.readouterr().out


def test_running_the_package_as_a_module_exits_zero(
    repo_root: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``python -m assert_subclause_citations`` scans src/ and exits with it.

    The scan reads the tree the cwd names, so the cwd is the repository root
    here rather than wherever pytest was started.
    """
    monkeypatch.chdir(repo_root)
    with pytest.raises(SystemExit, match="^0$"):
        runpy.run_module("assert_subclause_citations")
