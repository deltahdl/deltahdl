"""Tests for lib.supplementary."""

import argparse
from pathlib import Path
from unittest.mock import MagicMock

import pytest

from lib.python.supplementary import (
    add_supplementary_args,
    build_supplementary_lines,
    check_supplementary_args,
    parse_supplementary_csv_args,
)


# --- check_supplementary_args ---


def test_check_supplementary_args_missing_figure_path() -> None:
    """Exits when a figure path does not exist."""
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", ([], []),
            figures={"4-1": Path("/nonexistent/fig.gv")},
            tables={},
            ignore_figures=[],
        )


def test_check_supplementary_args_missing_table_path() -> None:
    """Exits when a table path does not exist."""
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", ([], []),
            figures={},
            tables={"4-1": Path("/nonexistent/tbl.md")},
            ignore_figures=[],
        )


def test_check_supplementary_args_missing_figure_label(tmp_path) -> None:
    """Exits when LRM requires a figure not provided."""
    fig = tmp_path / "fig.gv"
    fig.write_text("")
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", (["4-1", "4-2"], []),
            figures={"4-1": fig},
            tables={},
            ignore_figures=[],
        )


def test_check_supplementary_args_ignored_figure(tmp_path) -> None:
    """Does not exit when missing figure is in ignore list."""
    fig = tmp_path / "fig.gv"
    fig.write_text("")
    result = check_supplementary_args(
        "4", (["4-1", "4-2"], []),
        figures={"4-1": fig},
        tables={},
        ignore_figures=["4-2"],
    )
    assert result == ["4-1", "4-2"]


def test_check_supplementary_args_missing_table_label() -> None:
    """Exits when LRM requires a table not provided."""
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", ([], ["4-1"]),
            figures={},
            tables={},
            ignore_figures=[],
        )


def test_check_supplementary_args_all_provided(tmp_path) -> None:
    """Returns labels when all figures and tables are provided."""
    fig = tmp_path / "fig.gv"
    fig.write_text("")
    tbl = tmp_path / "tbl.md"
    tbl.write_text("")
    result = check_supplementary_args(
        "4", (["4-1"], ["4-1"]),
        figures={"4-1": fig},
        tables={"4-1": tbl},
        ignore_figures=[],
    )
    assert result == ["4-1", "4-1"]


def test_check_supplementary_args_no_labels() -> None:
    """Returns empty list when LRM has no figures or tables."""
    result = check_supplementary_args(
        "4", ([], []),
        figures={},
        tables={},
        ignore_figures=[],
    )
    assert not result


# --- build_supplementary_lines ---


def test_build_supplementary_lines_empty() -> None:
    """Returns empty string when no figures or tables."""
    assert build_supplementary_lines(figures={}, tables={}) == ""


def test_build_supplementary_lines_figure_reference() -> None:
    """Includes figure reference with label from key."""
    result = build_supplementary_lines(
        figures={"4-1": Path("fig.gv")}, tables={},
    )
    assert "Consult Figure 4-1" in result


def test_build_supplementary_lines_figure_format() -> None:
    """Includes figure format annotation."""
    result = build_supplementary_lines(
        figures={"4-1": Path("fig.gv")}, tables={},
    )
    assert "(DOT GraphViz)" in result


def test_build_supplementary_lines_table_reference() -> None:
    """Includes table reference with label from key."""
    result = build_supplementary_lines(
        figures={}, tables={"4-1": Path("tbl.md")},
    )
    assert "Consult Table 4-1" in result


def test_build_supplementary_lines_table_format() -> None:
    """Includes table format annotation."""
    result = build_supplementary_lines(
        figures={}, tables={"4-1": Path("tbl.md")},
    )
    assert "(Markdown)" in result


def test_build_supplementary_lines_both_figure() -> None:
    """Both mode includes figure reference."""
    result = build_supplementary_lines(
        figures={"4-1": Path("fig.gv")},
        tables={"4-1": Path("tbl.md")},
    )
    assert "Figure 4-1" in result


def test_build_supplementary_lines_both_table() -> None:
    """Both mode includes table reference."""
    result = build_supplementary_lines(
        figures={"4-1": Path("fig.gv")},
        tables={"4-1": Path("tbl.md")},
    )
    assert "Table 4-1" in result


# --- parse_supplementary_csv_args ---


def test_parse_supplementary_csv_args_empty_figures() -> None:
    """Empty figures string becomes empty dict."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert args.figures == {}


def test_parse_supplementary_csv_args_empty_tables() -> None:
    """Empty tables string becomes empty dict."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert args.tables == {}


def test_parse_supplementary_csv_args_empty_ignore_figures() -> None:
    """Empty ignore_figures string becomes empty list."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert not args.ignore_figures


def test_parse_supplementary_csv_args_figures() -> None:
    """Comma-separated key=path figures become dict with dash keys."""
    args = MagicMock()
    args.figures = "4_1=a.gv, 4_2=b.gv"
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert args.figures == {"4-1": Path("a.gv"), "4-2": Path("b.gv")}


def test_parse_supplementary_csv_args_tables() -> None:
    """Comma-separated key=path tables become dict with dash keys."""
    args = MagicMock()
    args.figures = ""
    args.tables = "22_1=c.md"
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert args.tables == {"22-1": Path("c.md")}


def test_parse_supplementary_csv_args_ignore_figures() -> None:
    """Comma-separated ignore_figures become string list."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = "4-1, 4-2"
    parse_supplementary_csv_args(args)
    assert args.ignore_figures == ["4-1", "4-2"]


def test_parse_supplementary_csv_args_strips_whitespace() -> None:
    """Whitespace around items is stripped."""
    args = MagicMock()
    args.figures = " 4_1=a.gv , "
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert args.figures == {"4-1": Path("a.gv")}


# --- add_supplementary_args ---


def test_add_supplementary_args_figures_default() -> None:
    """add_supplementary_args registers --figures with empty default."""
    parser = argparse.ArgumentParser()
    add_supplementary_args(parser)
    assert parser.parse_args([]).figures == ""


def test_add_supplementary_args_tables_default() -> None:
    """add_supplementary_args registers --tables with empty default."""
    parser = argparse.ArgumentParser()
    add_supplementary_args(parser)
    assert parser.parse_args([]).tables == ""


def test_add_supplementary_args_ignore_figures_default() -> None:
    """add_supplementary_args registers --ignore-figures with empty default."""
    parser = argparse.ArgumentParser()
    add_supplementary_args(parser)
    assert parser.parse_args([]).ignore_figures == ""
