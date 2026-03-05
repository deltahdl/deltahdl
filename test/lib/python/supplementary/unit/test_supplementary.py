"""Tests for lib.supplementary."""

from pathlib import Path
from unittest.mock import MagicMock

import pytest

from lib.python.supplementary import (
    add_supplementary_args,
    build_supplementary_lines,
    check_supplementary_args,
    label_from_gv,
    label_from_md,
    parse_supplementary_csv_args,
    shorthand_from_label,
)


# --- label_from_gv ---


def test_label_from_gv_simple() -> None:
    """Converts Figure_4_1.gv to 'Figure 4-1'."""
    assert label_from_gv(Path("Figure_4_1.gv")) == "Figure 4-1"


def test_label_from_gv_multidigit() -> None:
    """Converts Figure_22_13.gv to 'Figure 22-13'."""
    assert label_from_gv(Path("Figure_22_13.gv")) == "Figure 22-13"


def test_label_from_gv_annex() -> None:
    """Converts Figure_A_1.gv to 'Figure A-1'."""
    assert label_from_gv(Path("Figure_A_1.gv")) == "Figure A-1"


# --- label_from_md ---


def test_label_from_md_simple() -> None:
    """Converts TABLE_B_1.md to 'Table B-1'."""
    assert label_from_md(Path("TABLE_B_1.md")) == "Table B-1"


def test_label_from_md_numeric() -> None:
    """Converts TABLE_4_1.md to 'Table 4-1'."""
    assert label_from_md(Path("TABLE_4_1.md")) == "Table 4-1"


# --- shorthand_from_label ---


def test_shorthand_from_figure_label() -> None:
    """Extracts '4-1' from 'Figure 4-1'."""
    assert shorthand_from_label("Figure 4-1") == "4-1"


def test_shorthand_from_table_label() -> None:
    """Extracts 'B-1' from 'Table B-1'."""
    assert shorthand_from_label("Table B-1") == "B-1"


# --- check_supplementary_args ---


def test_check_supplementary_args_missing_figure_path() -> None:
    """Exits when a figure path does not exist."""
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", ([], []),
            figures=[Path("/nonexistent/Figure_4_1.gv")],
            tables=[],
            ignore_figures=[],
        )


def test_check_supplementary_args_missing_table_path() -> None:
    """Exits when a table path does not exist."""
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", ([], []),
            figures=[],
            tables=[Path("/nonexistent/TABLE_4_1.md")],
            ignore_figures=[],
        )


def test_check_supplementary_args_missing_figure_label(tmp_path) -> None:
    """Exits when LRM requires a figure not provided."""
    fig = tmp_path / "Figure_4_1.gv"
    fig.write_text("")
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", (["4-1", "4-2"], []),
            figures=[fig],
            tables=[],
            ignore_figures=[],
        )


def test_check_supplementary_args_ignored_figure(tmp_path) -> None:
    """Does not exit when missing figure is in ignore list."""
    fig = tmp_path / "Figure_4_1.gv"
    fig.write_text("")
    result = check_supplementary_args(
        "4", (["4-1", "4-2"], []),
        figures=[fig],
        tables=[],
        ignore_figures=["4-2"],
    )
    assert result == ["4-1", "4-2"]


def test_check_supplementary_args_missing_table_label() -> None:
    """Exits when LRM requires a table not provided."""
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", ([], ["4-1"]),
            figures=[],
            tables=[],
            ignore_figures=[],
        )


def test_check_supplementary_args_all_provided(tmp_path) -> None:
    """Returns labels when all figures and tables are provided."""
    fig = tmp_path / "Figure_4_1.gv"
    fig.write_text("")
    tbl = tmp_path / "TABLE_4_1.md"
    tbl.write_text("")
    result = check_supplementary_args(
        "4", (["4-1"], ["4-1"]),
        figures=[fig],
        tables=[tbl],
        ignore_figures=[],
    )
    assert result == ["4-1", "4-1"]


def test_check_supplementary_args_no_labels() -> None:
    """Returns empty list when LRM has no figures or tables."""
    result = check_supplementary_args(
        "4", ([], []),
        figures=[],
        tables=[],
        ignore_figures=[],
    )
    assert not result


# --- build_supplementary_lines ---


def test_build_supplementary_lines_empty() -> None:
    """Returns empty string when no figures or tables."""
    assert build_supplementary_lines(figures=[], tables=[]) == ""


def test_build_supplementary_lines_figure_reference() -> None:
    """Includes figure reference."""
    result = build_supplementary_lines(
        figures=[Path("Figure_4_1.gv")], tables=[],
    )
    assert "Consult Figure 4-1" in result


def test_build_supplementary_lines_figure_format() -> None:
    """Includes figure format annotation."""
    result = build_supplementary_lines(
        figures=[Path("Figure_4_1.gv")], tables=[],
    )
    assert "(DOT GraphViz)" in result


def test_build_supplementary_lines_table_reference() -> None:
    """Includes table reference."""
    result = build_supplementary_lines(
        figures=[], tables=[Path("TABLE_4_1.md")],
    )
    assert "Consult Table 4-1" in result


def test_build_supplementary_lines_table_format() -> None:
    """Includes table format annotation."""
    result = build_supplementary_lines(
        figures=[], tables=[Path("TABLE_4_1.md")],
    )
    assert "(Markdown)" in result


def test_build_supplementary_lines_both_figure() -> None:
    """Both mode includes figure reference."""
    result = build_supplementary_lines(
        figures=[Path("Figure_4_1.gv")],
        tables=[Path("TABLE_4_1.md")],
    )
    assert "Figure 4-1" in result


def test_build_supplementary_lines_both_table() -> None:
    """Both mode includes table reference."""
    result = build_supplementary_lines(
        figures=[Path("Figure_4_1.gv")],
        tables=[Path("TABLE_4_1.md")],
    )
    assert "Table 4-1" in result


# --- parse_supplementary_csv_args ---


def test_parse_supplementary_csv_args_empty_figures() -> None:
    """Empty figures string becomes empty list."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert not args.figures


def test_parse_supplementary_csv_args_empty_tables() -> None:
    """Empty tables string becomes empty list."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert not args.tables


def test_parse_supplementary_csv_args_empty_ignore_figures() -> None:
    """Empty ignore_figures string becomes empty list."""
    args = MagicMock()
    args.figures = ""
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert not args.ignore_figures


def test_parse_supplementary_csv_args_figures() -> None:
    """Comma-separated figures become Path list."""
    args = MagicMock()
    args.figures = "a.gv, b.gv"
    args.tables = "c.md"
    args.ignore_figures = "4-1, 4-2"
    parse_supplementary_csv_args(args)
    assert args.figures == [Path("a.gv"), Path("b.gv")]


def test_parse_supplementary_csv_args_tables() -> None:
    """Comma-separated tables become Path list."""
    args = MagicMock()
    args.figures = "a.gv, b.gv"
    args.tables = "c.md"
    args.ignore_figures = "4-1, 4-2"
    parse_supplementary_csv_args(args)
    assert args.tables == [Path("c.md")]


def test_parse_supplementary_csv_args_ignore_figures() -> None:
    """Comma-separated ignore_figures become string list."""
    args = MagicMock()
    args.figures = "a.gv, b.gv"
    args.tables = "c.md"
    args.ignore_figures = "4-1, 4-2"
    parse_supplementary_csv_args(args)
    assert args.ignore_figures == ["4-1", "4-2"]


def test_parse_supplementary_csv_args_strips_whitespace() -> None:
    """Whitespace around items is stripped."""
    args = MagicMock()
    args.figures = " a.gv , "
    args.tables = ""
    args.ignore_figures = ""
    parse_supplementary_csv_args(args)
    assert args.figures == [Path("a.gv")]


# --- add_supplementary_args ---


def test_add_supplementary_args_figures_default() -> None:
    """add_supplementary_args registers --figures with empty default."""
    import argparse
    parser = argparse.ArgumentParser()
    add_supplementary_args(parser)
    assert parser.parse_args([]).figures == ""


def test_add_supplementary_args_tables_default() -> None:
    """add_supplementary_args registers --tables with empty default."""
    import argparse
    parser = argparse.ArgumentParser()
    add_supplementary_args(parser)
    assert parser.parse_args([]).tables == ""


def test_add_supplementary_args_ignore_figures_default() -> None:
    """add_supplementary_args registers --ignore-figures with empty default."""
    import argparse
    parser = argparse.ArgumentParser()
    add_supplementary_args(parser)
    assert parser.parse_args([]).ignore_figures == ""
