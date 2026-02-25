"""Unit tests for implement_clause.common."""

from pathlib import Path

import pytest

from implement_clause.common import (
    build_hierarchy,
    build_supplementary_lines,
    find_supplementary_files,
    load_lrm_titles,
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


# ---- find_supplementary_files ----------------------------------------------


_FIGURES_DIR = Path(
    "/Users/jdrowne/Library/CloudStorage/"
    "GoogleDrive-jdrowne@10ulabs.com/Shared drives/"
    "10U Labs Shared Drive/Standards/SystemVerilog/Figures"
)
_TABLES_DIR = Path(
    "/Users/jdrowne/Library/CloudStorage/"
    "GoogleDrive-jdrowne@10ulabs.com/Shared drives/"
    "10U Labs Shared Drive/Standards/SystemVerilog/Tables"
)


def test_find_supplementary_empty_when_dirs_missing(tmp_path, monkeypatch):
    """Returns empty list when Figures/Tables dirs don't exist."""
    monkeypatch.setattr(
        "implement_clause.common.FIGURES_DIR",
        tmp_path / "no_figures",
    )
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR",
        tmp_path / "no_tables",
    )
    assert not find_supplementary_files("4.4.3.1")


def test_find_supplementary_finds_figure(tmp_path, monkeypatch):
    """Finds Figure files matching the clause's top-level component."""
    figs = tmp_path / "Figures"
    figs.mkdir()
    gv = figs / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    monkeypatch.setattr("implement_clause.common.FIGURES_DIR", figs)
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR", tmp_path / "no_tables",
    )
    assert find_supplementary_files("4.4.3.1") == [("Figure 4-1", gv)]


def test_find_supplementary_finds_table(tmp_path, monkeypatch):
    """Finds Table files matching the clause's top-level component."""
    tabs = tmp_path / "Tables"
    tabs.mkdir()
    md = tabs / "TABLE_B_1.md"
    md.write_text("| keyword |\n")
    monkeypatch.setattr(
        "implement_clause.common.FIGURES_DIR", tmp_path / "no_figs",
    )
    monkeypatch.setattr("implement_clause.common.TABLES_DIR", tabs)
    assert find_supplementary_files("B") == [("Table B-1", md)]


def test_find_supplementary_ignores_other_clauses(tmp_path, monkeypatch):
    """Ignores files belonging to other clauses."""
    figs = tmp_path / "Figures"
    figs.mkdir()
    (figs / "Figure_4_1.gv").write_text("digraph {}")
    monkeypatch.setattr("implement_clause.common.FIGURES_DIR", figs)
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR", tmp_path / "no_tables",
    )
    assert not find_supplementary_files("6.24.1")


# ---- build_supplementary_lines ---------------------------------------------


def test_build_supplementary_lines_with_figure(tmp_path, monkeypatch):
    """Generates acknowledgment line for a .gv figure."""
    figs = tmp_path / "Figures"
    figs.mkdir()
    gv = figs / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    monkeypatch.setattr("implement_clause.common.FIGURES_DIR", figs)
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR", tmp_path / "no_tables",
    )
    lines = build_supplementary_lines("4")
    assert "Figure 4-1" in lines and "DOT GraphViz" in lines


def test_build_supplementary_lines_with_table(tmp_path, monkeypatch):
    """Generates acknowledgment line for a .md table."""
    tabs = tmp_path / "Tables"
    tabs.mkdir()
    md = tabs / "TABLE_B_1.md"
    md.write_text("| keyword |\n")
    monkeypatch.setattr(
        "implement_clause.common.FIGURES_DIR", tmp_path / "no_figs",
    )
    monkeypatch.setattr("implement_clause.common.TABLES_DIR", tabs)
    lines = build_supplementary_lines("B")
    assert "Table B-1" in lines and "Markdown" in lines


def test_build_supplementary_lines_empty_when_none(tmp_path, monkeypatch):
    """Returns empty string when no supplementary files found."""
    monkeypatch.setattr(
        "implement_clause.common.FIGURES_DIR", tmp_path / "no_figs",
    )
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR", tmp_path / "no_tables",
    )
    assert build_supplementary_lines("99") == ""
