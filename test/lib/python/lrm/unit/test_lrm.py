"""Tests for lib.lrm."""

from pathlib import Path

import pytest

from lib.python.lrm import extract_clause_text, load_lrm_titles, parse_subclauses


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


# ---- parse_subclauses ------------------------------------------------------


SAMPLE_NUMERIC = """\
Some preamble text.

4. Scheduling semantics

4.1 General
Some text about general scheduling.

4.2 Execution of a hardware model
More text here.

4.3 Event simulation
Event simulation details.

4.4 Stratified event scheduler
4.4.1 Preponed events region
Deep subclause text.
4.4.2 Active events region
More deep text.

5. Lexical conventions
5.1 Lexical tokens
"""

SAMPLE_ANNEX = """\
Some preamble.

Annex A
(normative)

Formal syntax

A.1 Source text
A.1.1 Library source text
Some text.
A.1.2 SystemVerilog source text
More text.

A.2 Declarations
A.2.1 Declaration types
A.2.1.1 Module parameter declarations
Deep text.

Annex B
(normative)

Keywords
"""


def test_parse_subclauses_numeric(tmp_path: Path) -> None:
    """Direct subclauses of a numeric clause are returned."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert parse_subclauses(lrm, "4") == {
        "4.1": "General",
        "4.2": "Execution of a hardware model",
        "4.3": "Event simulation",
        "4.4": "Stratified event scheduler",
    }


def test_parse_subclauses_deeper(tmp_path: Path) -> None:
    """Direct subclauses of a deeper clause are returned."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert parse_subclauses(lrm, "4.4") == {
        "4.4.1": "Preponed events region",
        "4.4.2": "Active events region",
    }


def test_parse_subclauses_no_children(tmp_path: Path) -> None:
    """Empty dict when a clause has no subclauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert parse_subclauses(lrm, "4.1") == {}


def test_parse_subclauses_annex(tmp_path: Path) -> None:
    """Direct subclauses of an annex are returned."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_ANNEX)
    assert parse_subclauses(lrm, "A") == {
        "A.1": "Source text",
        "A.2": "Declarations",
    }


def test_parse_subclauses_annex_deeper(tmp_path: Path) -> None:
    """Direct subclauses of an annex subclause are returned."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_ANNEX)
    assert parse_subclauses(lrm, "A.1") == {
        "A.1.1": "Library source text",
        "A.1.2": "SystemVerilog source text",
    }


# --- extract_clause_text ---


def test_extract_clause_text_numeric(tmp_path: Path) -> None:
    """Full text of a numeric clause is extracted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert extract_clause_text(lrm, "4") == (
        "4. Scheduling semantics\n"
        "\n"
        "4.1 General\n"
        "Some text about general scheduling.\n"
        "\n"
        "4.2 Execution of a hardware model\n"
        "More text here.\n"
        "\n"
        "4.3 Event simulation\n"
        "Event simulation details.\n"
        "\n"
        "4.4 Stratified event scheduler\n"
        "4.4.1 Preponed events region\n"
        "Deep subclause text.\n"
        "4.4.2 Active events region\n"
        "More deep text."
    )


def test_extract_clause_text_subclause(tmp_path: Path) -> None:
    """Full text of a subclause is extracted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert extract_clause_text(lrm, "4.1") == (
        "4.1 General\n"
        "Some text about general scheduling."
    )


def test_extract_clause_text_annex(tmp_path: Path) -> None:
    """Full text of an annex is extracted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_ANNEX)
    assert extract_clause_text(lrm, "A") == (
        "Annex A\n"
        "(normative)\n"
        "\n"
        "Formal syntax\n"
        "\n"
        "A.1 Source text\n"
        "A.1.1 Library source text\n"
        "Some text.\n"
        "A.1.2 SystemVerilog source text\n"
        "More text.\n"
        "\n"
        "A.2 Declarations\n"
        "A.2.1 Declaration types\n"
        "A.2.1.1 Module parameter declarations\n"
        "Deep text."
    )


def test_extract_clause_text_last_clause(tmp_path: Path) -> None:
    """Text is extracted when clause extends to end of file."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert extract_clause_text(lrm, "5.1") == "5.1 Lexical tokens"


def test_extract_clause_text_not_found(tmp_path: Path) -> None:
    """Empty string when the clause is not found."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(SAMPLE_NUMERIC)
    assert extract_clause_text(lrm, "99") == ""
