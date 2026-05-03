"""Unit tests for document_dependency_graph.oracles."""

from pathlib import Path
from unittest.mock import patch

import pytest

from document_dependency_graph.oracles import (
    build_prerequisites_prompt,
    build_proof_sentence_prompt,
    compute_prerequisites,
    compute_proof_sentence,
    parse_prerequisites,
    parse_proof_sentence,
)


# --- build_proof_sentence_prompt -------------------------------------------


def test_proof_prompt_names_subclause(make_lrm: Path) -> None:
    """The proof-sentence prompt names the asking subclause §X."""
    prompt = build_proof_sentence_prompt("4.4", "3.14.3", str(make_lrm))
    assert "§4.4" in prompt


def test_proof_prompt_names_dependency(make_lrm: Path) -> None:
    """The proof-sentence prompt names the dependency §Y."""
    prompt = build_proof_sentence_prompt("4.4", "3.14.3", str(make_lrm))
    assert "§3.14.3" in prompt


def test_proof_prompt_includes_lrm_read_instruction(make_lrm: Path) -> None:
    """The proof-sentence prompt tells Claude to read the LRM at the path."""
    prompt = build_proof_sentence_prompt("4.4", "3.14.3", str(make_lrm))
    assert str(make_lrm) in prompt


def test_proof_prompt_requests_quoted_sentence(make_lrm: Path) -> None:
    """The proof-sentence prompt asks for a single quoted sentence."""
    prompt = build_proof_sentence_prompt("4.4", "3.14.3", str(make_lrm))
    assert "sentence" in prompt


# --- parse_proof_sentence ---------------------------------------------------


def test_parse_proof_sentence_returns_string() -> None:
    """parse_proof_sentence extracts the JSON string body."""
    raw = '"Module instantiation requires the elaborated definition."'
    assert parse_proof_sentence(raw) == (
        "Module instantiation requires the elaborated definition."
    )


def test_parse_proof_sentence_strips_fences() -> None:
    """parse_proof_sentence handles a fenced ```json string```."""
    raw = '```json\n"Reg variables shall be assignable."\n```'
    assert parse_proof_sentence(raw) == "Reg variables shall be assignable."


def test_parse_proof_sentence_rejects_empty_string() -> None:
    """parse_proof_sentence rejects an empty string."""
    with pytest.raises(ValueError):
        parse_proof_sentence('""')


def test_parse_proof_sentence_picks_last_string_after_prose() -> None:
    """parse_proof_sentence picks the trailing JSON string past reasoning prose."""
    raw = (
        "Based on §3, the only material reference is in"
        " §3.13(h): \"enclosed by the (* and *) constructs (see"
        " 5.12).\"\n\n"
        '"the attribute_instance syntax and its dedicated name space"'
    )
    assert parse_proof_sentence(raw) == (
        "the attribute_instance syntax and its dedicated name space"
    )


def test_parse_proof_sentence_rejects_non_string() -> None:
    """parse_proof_sentence rejects a non-string JSON value."""
    with pytest.raises(ValueError):
        parse_proof_sentence("123")


# --- compute_proof_sentence ------------------------------------------------


def test_compute_proof_sentence_returns_parsed_text(make_lrm: Path) -> None:
    """compute_proof_sentence returns the oracle's quoted sentence."""
    with patch(
        "document_dependency_graph.oracles.run_oracle_call",
        return_value='"Module instantiation requires elaboration."',
    ):
        result = compute_proof_sentence(
            "4.4", "3.14.3", str(make_lrm), model="opus",
        )
    assert result == "Module instantiation requires elaboration."


def test_compute_proof_sentence_passes_prompt(make_lrm: Path) -> None:
    """compute_proof_sentence sends the proof-sentence prompt to the oracle."""
    with patch(
        "document_dependency_graph.oracles.run_oracle_call",
        return_value='"x."',
    ) as mock_call:
        compute_proof_sentence(
            "4.4", "3.14.3", str(make_lrm), model="opus",
        )
    assert "§3.14.3" in mock_call.call_args[0][0]


def test_compute_proof_sentence_passes_model(make_lrm: Path) -> None:
    """compute_proof_sentence forwards the model to the oracle."""
    with patch(
        "document_dependency_graph.oracles.run_oracle_call",
        return_value='"x."',
    ) as mock_call:
        compute_proof_sentence(
            "4.4", "3.14.3", str(make_lrm), model="haiku",
        )
    assert mock_call.call_args[1]["model"] == "haiku"


# --- build_prerequisites_prompt --------------------------------------------


def test_prereq_prompt_names_subclause(make_lrm: Path) -> None:
    """The prerequisites prompt names §X."""
    prompt = build_prerequisites_prompt("4.4", "3.14.3", str(make_lrm))
    assert "§4.4" in prompt


def test_prereq_prompt_names_dependency(make_lrm: Path) -> None:
    """The prerequisites prompt names §Y."""
    prompt = build_prerequisites_prompt("4.4", "3.14.3", str(make_lrm))
    assert "§3.14.3" in prompt


def test_prereq_prompt_asks_what_must_exist(make_lrm: Path) -> None:
    """The prerequisites prompt asks what §Y must already provide."""
    prompt = build_prerequisites_prompt("4.4", "3.14.3", str(make_lrm))
    assert "already" in prompt


# --- parse_prerequisites ---------------------------------------------------


def test_parse_prerequisites_returns_string() -> None:
    """parse_prerequisites returns the JSON string body."""
    raw = '"the elaborated module definition"'
    assert parse_prerequisites(raw) == "the elaborated module definition"


def test_parse_prerequisites_rejects_non_string() -> None:
    """parse_prerequisites rejects a non-string JSON value."""
    with pytest.raises(ValueError):
        parse_prerequisites("[]")


def test_parse_prerequisites_rejects_empty_string() -> None:
    """parse_prerequisites rejects an empty string."""
    with pytest.raises(ValueError):
        parse_prerequisites('""')


# --- compute_prerequisites -------------------------------------------------


def test_compute_prerequisites_returns_parsed_text(make_lrm: Path) -> None:
    """compute_prerequisites returns the oracle's parsed string."""
    with patch(
        "document_dependency_graph.oracles.run_oracle_call",
        return_value='"elaborated definitions"',
    ):
        result = compute_prerequisites(
            "4.4", "3.14.3", str(make_lrm), model="opus",
        )
    assert result == "elaborated definitions"


def test_compute_prerequisites_passes_prereq_prompt(make_lrm: Path) -> None:
    """compute_prerequisites sends the prerequisites prompt to the oracle."""
    with patch(
        "document_dependency_graph.oracles.run_oracle_call",
        return_value='"x"',
    ) as mock_call:
        compute_prerequisites(
            "4.4", "3.14.3", str(make_lrm), model="opus",
        )
    assert "prerequisites oracle" in mock_call.call_args[0][0]


def test_compute_prerequisites_passes_model(make_lrm: Path) -> None:
    """compute_prerequisites forwards the model to the oracle."""
    with patch(
        "document_dependency_graph.oracles.run_oracle_call",
        return_value='"x"',
    ) as mock_call:
        compute_prerequisites(
            "4.4", "3.14.3", str(make_lrm), model="haiku",
        )
    assert mock_call.call_args[1]["model"] == "haiku"
