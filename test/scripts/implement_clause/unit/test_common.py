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


def test_load_subclause_titles(tmp_path):
    """Extracts dot-separated subclause titles like '4.1 General'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_SAMPLE_LRM)
    titles = load_lrm_titles(lrm)
    assert titles["3.1"] == "General"
    assert titles["4.4.3.1"] == "Preponed PLI region"
    assert titles["A.8.1"] == "Concatenations"


def test_load_top_level_clause_titles(tmp_path):
    """Extracts top-level numeric clause titles like '4. Scheduling semantics'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_SAMPLE_LRM)
    titles = load_lrm_titles(lrm)
    assert titles["3"] == "Design and verification building blocks"
    assert titles["4"] == "Scheduling semantics"


def test_load_annex_header_titles(tmp_path):
    """Extracts multi-line annex headers like 'Annex B\\n(normative)\\n\\nKeywords'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_SAMPLE_LRM)
    titles = load_lrm_titles(lrm)
    assert titles["A"] == "(normative) Formal syntax"
    assert titles["B"] == "(normative) Keywords"
    assert titles["P"] == "(informative) Glossary"


def test_load_missing_file(tmp_path):
    """Returns empty dict when file does not exist."""
    titles = load_lrm_titles(tmp_path / "no_such_file.txt")
    assert titles == {}


# ---- build_hierarchy --------------------------------------------------------


class TestBuildHierarchyNumeric:
    """Tests for numeric (non-annex) clauses."""

    def test_depth_1(self):
        h = build_hierarchy("4")
        assert h["is_annex"] is False
        assert h["clause_number"] == "4"
        assert h["ancestors"] == []
        assert h["subclause"] == "4"

    def test_depth_2(self):
        h = build_hierarchy("4.1")
        assert h["is_annex"] is False
        assert h["clause_number"] == "4"
        assert h["ancestors"] == []
        assert h["subclause"] == "4.1"

    def test_depth_3(self):
        h = build_hierarchy("6.24.1")
        assert h["is_annex"] is False
        assert h["clause_number"] == "6"
        assert h["principle"] == "6.1"
        assert h["ancestors"] == ["6.24"]
        assert h["subclause"] == "6.24.1"

    def test_depth_4(self):
        h = build_hierarchy("4.4.3.1")
        assert h["is_annex"] is False
        assert h["clause_number"] == "4"
        assert h["principle"] == "4.1"
        assert h["ancestors"] == ["4.4", "4.4.3"]
        assert h["subclause"] == "4.4.3.1"

    def test_depth_5(self):
        h = build_hierarchy("4.4.3.1.2")
        assert h["is_annex"] is False
        assert h["clause_number"] == "4"
        assert h["principle"] == "4.1"
        assert h["ancestors"] == ["4.4", "4.4.3", "4.4.3.1"]
        assert h["subclause"] == "4.4.3.1.2"


class TestBuildHierarchyAnnex:
    """Tests for annex (uppercase letter) clauses."""

    def test_depth_1(self):
        h = build_hierarchy("B")
        assert h["is_annex"] is True
        assert h["collection"] == "Annex B"
        assert h["letter"] == "B"
        assert h["ancestors"] == []
        assert h["subclause"] == "B"

    def test_depth_2(self):
        h = build_hierarchy("A.8")
        assert h["is_annex"] is True
        assert h["collection"] == "Annex A"
        assert h["letter"] == "A"
        assert h["principles"] == "A.8"
        assert h["ancestors"] == []
        assert h["subclause"] == "A.8"

    def test_depth_3(self):
        h = build_hierarchy("A.8.1")
        assert h["is_annex"] is True
        assert h["collection"] == "Annex A"
        assert h["principles"] == "A.8"
        assert h["ancestors"] == []
        assert h["subclause"] == "A.8.1"

    def test_depth_4(self):
        h = build_hierarchy("A.7.5.3")
        assert h["is_annex"] is True
        assert h["collection"] == "Annex A"
        assert h["principles"] == "A.7"
        assert h["ancestors"] == ["A.7.5"]
        assert h["subclause"] == "A.7.5.3"

    def test_depth_5(self):
        h = build_hierarchy("A.7.5.3.1")
        assert h["is_annex"] is True
        assert h["collection"] == "Annex A"
        assert h["principles"] == "A.7"
        assert h["ancestors"] == ["A.7.5", "A.7.5.3"]
        assert h["subclause"] == "A.7.5.3.1"


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
    assert find_supplementary_files("4.4.3.1") == []


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
    result = find_supplementary_files("4.4.3.1")
    assert len(result) == 1
    assert result[0][0] == "Figure 4-1"
    assert result[0][1] == gv


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
    result = find_supplementary_files("B")
    assert len(result) == 1
    assert result[0][0] == "Table B-1"
    assert result[0][1] == md


def test_find_supplementary_ignores_other_clauses(tmp_path, monkeypatch):
    """Ignores files belonging to other clauses."""
    figs = tmp_path / "Figures"
    figs.mkdir()
    (figs / "Figure_4_1.gv").write_text("digraph {}")
    monkeypatch.setattr("implement_clause.common.FIGURES_DIR", figs)
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR", tmp_path / "no_tables",
    )
    assert find_supplementary_files("6.24.1") == []


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
    assert "Figure 4-1" in lines
    assert "DOT GraphViz" in lines


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
    assert "Table B-1" in lines
    assert "Markdown" in lines


def test_build_supplementary_lines_empty_when_none(tmp_path, monkeypatch):
    """Returns empty string when no supplementary files found."""
    monkeypatch.setattr(
        "implement_clause.common.FIGURES_DIR", tmp_path / "no_figs",
    )
    monkeypatch.setattr(
        "implement_clause.common.TABLES_DIR", tmp_path / "no_tables",
    )
    assert build_supplementary_lines("99") == ""
