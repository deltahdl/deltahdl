"""Unit tests for implement_subclause."""

from unittest.mock import MagicMock, patch

import pytest

from implement_subclause import (
    build_hierarchy,
    build_supplementary_lines,
    check_supplementary_args,
    format_prompt,
    invoke_claude,
    load_lrm_titles,
    run_prompt,
)


# ---- load_lrm_titles -------------------------------------------------------


_SAMPLE_LRM = """\
IEEE Std 1800-2023

3. Design and verification building blocks
3.1 General
This clause describes the following:
3.2 Design elements

4. Scheduling semantics
4.1 General
This clause describes the scheduling semantics.
4.4 Stratified event scheduler
4.4.3 The PLI callback control points
4.4.3.1 Preponed PLI region

A.1 Source text
A.1.1 Library source text
A.8 Classes
A.8.1 Concatenations

Annex A
(normative)

Formal syntax

Annex B
(normative)

Keywords
SystemVerilog reserves the keywords listed in Table B.1.

Annex P
(informative)

Glossary
"""


class TestLoadLrmTitles:
    """Tests for load_lrm_titles."""

    @pytest.fixture()
    def titles(self, tmp_path):
        """Load titles from the sample LRM text."""
        lrm = tmp_path / "lrm.txt"
        lrm.write_text(_SAMPLE_LRM)
        return load_lrm_titles(lrm)

    @pytest.mark.parametrize("key, expected", [
        ("3.1", "General"),
        ("4.4.3.1", "Preponed PLI region"),
        ("A.8.1", "Concatenations"),
    ])
    def test_subclause_titles(self, titles, key, expected):
        """Extracts dot-separated subclause titles."""
        assert titles[key] == expected

    @pytest.mark.parametrize("key, expected", [
        ("3", "Design and verification building blocks"),
        ("4", "Scheduling semantics"),
    ])
    def test_top_level_clause_titles(self, titles, key, expected):
        """Extracts top-level numeric clause titles."""
        assert titles[key] == expected

    @pytest.mark.parametrize("key, expected", [
        ("A", "(normative) Formal syntax"),
        ("B", "(normative) Keywords"),
        ("P", "(informative) Glossary"),
    ])
    def test_annex_header_titles(self, titles, key, expected):
        """Extracts multi-line annex header titles."""
        assert titles[key] == expected


def test_load_missing_file(tmp_path):
    """Returns empty dict when file does not exist."""
    assert not load_lrm_titles(tmp_path / "no_such_file.txt")


# ---- build_hierarchy --------------------------------------------------------


class TestBuildHierarchyNumeric:
    """Tests for numeric (non-annex) clauses."""

    def test_depth_1(self):
        """Clause '4' produces depth-1 numeric hierarchy."""
        assert build_hierarchy("4") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4",
        }

    def test_depth_2(self):
        """Clause '4.1' produces depth-2 numeric hierarchy."""
        assert build_hierarchy("4.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4.1",
        }

    def test_depth_3(self):
        """Clause '6.24.1' produces depth-3 numeric hierarchy."""
        assert build_hierarchy("6.24.1") == {
            "is_annex": False,
            "clause_number": "6",
            "principle": "6.1",
            "ancestors": ["6.24"],
            "subclause": "6.24.1",
        }

    def test_depth_4(self):
        """Clause '4.4.3.1' produces depth-4 numeric hierarchy."""
        assert build_hierarchy("4.4.3.1") == {
            "is_annex": False,
            "clause_number": "4",
            "principle": "4.1",
            "ancestors": ["4.4", "4.4.3"],
            "subclause": "4.4.3.1",
        }

    def test_depth_5(self):
        """Clause '4.4.3.1.2' produces depth-5 numeric hierarchy."""
        assert build_hierarchy("4.4.3.1.2") == {
            "is_annex": False,
            "clause_number": "4",
            "principle": "4.1",
            "ancestors": ["4.4", "4.4.3", "4.4.3.1"],
            "subclause": "4.4.3.1.2",
        }


class TestBuildHierarchyAnnex:
    """Tests for annex (uppercase letter) clauses."""

    def test_depth_1(self):
        """Clause 'B' produces depth-1 annex hierarchy."""
        assert build_hierarchy("B") == {
            "is_annex": True,
            "collection": "Annex B",
            "letter": "B",
            "ancestors": [],
            "subclause": "B",
        }

    def test_depth_2(self):
        """Clause 'A.8' produces depth-2 annex hierarchy."""
        assert build_hierarchy("A.8") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "principles": "A.8",
            "ancestors": [],
            "subclause": "A.8",
        }

    def test_depth_3(self):
        """Clause 'A.8.1' produces depth-3 annex hierarchy."""
        assert build_hierarchy("A.8.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "principles": "A.8",
            "ancestors": [],
            "subclause": "A.8.1",
        }

    def test_depth_4(self):
        """Clause 'A.7.5.3' produces depth-4 annex hierarchy."""
        assert build_hierarchy("A.7.5.3") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "principles": "A.7",
            "ancestors": ["A.7.5"],
            "subclause": "A.7.5.3",
        }

    def test_depth_5(self):
        """Clause 'A.7.5.3.1' produces depth-5 annex hierarchy."""
        assert build_hierarchy("A.7.5.3.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "principles": "A.7",
            "ancestors": ["A.7.5", "A.7.5.3"],
            "subclause": "A.7.5.3.1",
        }


# ---- build_supplementary_lines ---------------------------------------------


def test_build_supplementary_lines_with_figure(tmp_path):
    """Generates acknowledgment line for a .gv figure."""
    gv = tmp_path / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    lines = build_supplementary_lines(figures=[gv], tables=[])
    assert "Figure 4-1" in lines and "DOT GraphViz" in lines


def test_build_supplementary_lines_with_table(tmp_path):
    """Generates acknowledgment line for a .md table."""
    md = tmp_path / "TABLE_B_1.md"
    md.write_text("| keyword |\n")
    lines = build_supplementary_lines(figures=[], tables=[md])
    assert "Table B-1" in lines and "Markdown" in lines


def test_build_supplementary_lines_empty_when_none():
    """Returns empty string when no figures or tables provided."""
    assert build_supplementary_lines(figures=[], tables=[]) == ""


def test_build_supplementary_lines_includes_figure(tmp_path):
    """Multiple supplementary files include the figure label."""
    gv = tmp_path / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    md = tmp_path / "TABLE_4_1.md"
    md.write_text("| col |\n")
    assert "Figure 4-1" in build_supplementary_lines(figures=[gv], tables=[md])


def test_build_supplementary_lines_includes_table(tmp_path):
    """Multiple supplementary files include the table label."""
    gv = tmp_path / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    md = tmp_path / "TABLE_4_1.md"
    md.write_text("| col |\n")
    assert "Table 4-1" in build_supplementary_lines(figures=[gv], tables=[md])


# ---- check_supplementary_args ---------------------------------------------


_LRM_WITH_FIGURES_AND_TABLES = """\
List of figures
Figure 4-1\u2014Event scheduling regions

List of tables
Table 4-1\u2014PLI callbacks
"""

_LRM_NO_SUPPLEMENTARY = """\
List of figures

List of tables
"""


def test_check_fails_when_figure_missing(tmp_path):
    """Fails when LRM lists a figure but no --figures or --ignore-figures."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURES_AND_TABLES)
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", lrm, figures=[], tables=[], ignore_figures=[],
        )


def test_check_passes_when_figure_ignored(tmp_path):
    """Passes when figure is in --ignore-figures."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURES_AND_TABLES)
    tbl = tmp_path / "TABLE_4_1.md"
    tbl.write_text("| col |\n")
    assert check_supplementary_args(
        "4", lrm, figures=[], tables=[tbl], ignore_figures=["4-1"],
    ) is None


def test_check_passes_when_all_supplementary_provided(tmp_path):
    """Passes when all figures and tables are provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURES_AND_TABLES)
    fig = tmp_path / "Figure_4_1.gv"
    fig.write_text("digraph {}")
    tbl = tmp_path / "TABLE_4_1.md"
    tbl.write_text("| col |\n")
    assert check_supplementary_args(
        "4", lrm, figures=[fig], tables=[tbl], ignore_figures=[],
    ) is None


def test_check_fails_when_table_missing(tmp_path):
    """Fails when LRM lists a table but no --tables provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURES_AND_TABLES)
    fig = tmp_path / "Figure_4_1.gv"
    fig.write_text("digraph {}")
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "4", lrm, figures=[fig], tables=[], ignore_figures=[],
        )


def test_check_fails_when_figure_path_missing(tmp_path):
    """Fails when a --figures path does not exist on disk."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_NO_SUPPLEMENTARY)
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "99", lrm,
            figures=[tmp_path / "nonexistent.gv"],
            tables=[], ignore_figures=[],
        )


def test_check_fails_when_table_path_missing(tmp_path):
    """Fails when a --tables path does not exist on disk."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_NO_SUPPLEMENTARY)
    with pytest.raises(SystemExit):
        check_supplementary_args(
            "99", lrm,
            figures=[],
            tables=[tmp_path / "nonexistent.md"],
            ignore_figures=[],
        )


def test_check_passes_when_no_supplementary(tmp_path):
    """Passes when clause has no figures or tables in LRM."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_NO_SUPPLEMENTARY)
    assert check_supplementary_args(
        "99", lrm, figures=[], tables=[], ignore_figures=[],
    ) is None


# ---- load_lrm_titles: annex without normative/informative -----------------


def test_load_annex_title_without_normative(tmp_path):
    """Annex header with title but no (normative)/(informative) line."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("Annex Z\n\nCustom Title\n")
    assert load_lrm_titles(lrm)["Z"] == "Custom Title"


def test_load_annex_no_title_found(tmp_path):
    """Annex header followed only by blank lines produces no entry."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("Annex Q\n\n\n\n\n\n\n")
    assert "Q" not in load_lrm_titles(lrm)


# ---- format_prompt --------------------------------------------------------


def test_format_prompt_includes_supplementary():
    """Supplementary text appears in the formatted prompt."""
    result = format_prompt(
        "- hierarchy\n", "4.1", "~/LRM.txt",
        issue=6, supplementary="- Table 4-1\n",
    )
    assert "Table 4-1" in result


def test_format_prompt_includes_single_overview():
    """Single overview subclause appears in the formatted prompt."""
    result = format_prompt(
        "- hierarchy\n", "4.4.3.1", "~/LRM.txt",
        issue=6, overviews=["4.1"],
    )
    assert "Thoroughly understand 4.1 per LRM" in result


def test_format_prompt_includes_first_of_multiple_overviews():
    """First overview subclause appears when multiple are provided."""
    result = format_prompt(
        "- hierarchy\n", "4.4.3.1", "~/LRM.txt",
        issue=6, overviews=["4.1", "4.4"],
    )
    assert "Thoroughly understand 4.1 per LRM" in result


def test_format_prompt_includes_second_of_multiple_overviews():
    """Second overview subclause appears when multiple are provided."""
    result = format_prompt(
        "- hierarchy\n", "4.4.3.1", "~/LRM.txt",
        issue=6, overviews=["4.1", "4.4"],
    )
    assert "Thoroughly understand 4.4 per LRM" in result


def test_format_prompt_excludes_overviews_by_default():
    """No overview line appears when overviews is not provided."""
    result = format_prompt(
        "- hierarchy\n", "4.1", "~/LRM.txt",
        issue=6,
    )
    assert "Thoroughly understand 4.1 per LRM" not in result


# ---- invoke_claude --------------------------------------------------------


@patch("implement_subclause.subprocess.Popen")
def test_invoke_claude_success(mock_popen):
    """invoke_claude streams prompt to Claude CLI and returns on success."""
    proc = MagicMock()
    proc.communicate.return_value = (None, None)
    proc.returncode = 0
    proc.__enter__ = MagicMock(return_value=proc)
    proc.__exit__ = MagicMock(return_value=False)
    mock_popen.return_value = proc
    invoke_claude("test prompt", model="opus")
    assert proc.communicate.called


@patch("implement_subclause.sys.exit")
@patch("implement_subclause.subprocess.Popen")
def test_invoke_claude_failure_exits(mock_popen, mock_exit):
    """invoke_claude calls sys.exit on non-zero return code."""
    proc = MagicMock()
    proc.communicate.return_value = (None, None)
    proc.returncode = 1
    proc.__enter__ = MagicMock(return_value=proc)
    proc.__exit__ = MagicMock(return_value=False)
    mock_popen.return_value = proc
    invoke_claude("test prompt")
    assert mock_exit.called


# ---- run_prompt -----------------------------------------------------------


@patch("implement_subclause.invoke_claude")
def test_run_prompt_calls_invoke(mock_invoke, tmp_path):
    """run_prompt loads titles, builds prompt, and invokes Claude."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("4. Scheduling semantics\n4.1 General\n")
    build_fn = MagicMock(return_value="generated prompt")
    run_prompt(build_fn, lrm, "4.1", issue=6, model="sonnet")
    assert mock_invoke.call_args[0][0] == "generated prompt"
