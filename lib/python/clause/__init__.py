"""Utilities for parsing and formatting LRM clause numbers."""

import re
from typing import Any


STAGE_TO_PREFIX: dict[str, str] = {
    "preprocessor": "test_preprocessor_",
    "lexer": "test_lexer_",
    "parser": "test_parser_",
    "elaborator": "test_elaborator_",
    "simulator": "test_simulator_",
    "synthesizer": "test_synthesizer_",
}


def clause_to_filename(prefix: str, clause: str) -> str:
    """Convert prefix + clause to a target filename (without .cpp)."""
    if clause.startswith("non-lrm"):
        topic = clause.split(":", 1)[1] if ":" in clause else "misc"
        return f"test_non_lrm_{topic}"
    prefix = prefix.rstrip("_")
    if re.match(r"^[A-Z]$", clause):
        return f"{prefix}_annex_{clause.lower()}"
    annex_match = re.match(r"^([A-Z])\.(.+)$", clause)
    if annex_match:
        letter = annex_match.group(1).lower()
        parts = annex_match.group(2).split(".")
        padded = "_".join(p.zfill(2) for p in parts)
        return f"{prefix}_annex_{letter}_{padded}"
    parts = clause.split(".")
    padded = "_".join(p.zfill(2) for p in parts)
    return f"{prefix}_clause_{padded}"


def build_hierarchy(clause: str) -> dict[str, Any]:
    """Derive template variables from a clause string.

    Returns a dict with keys:
    - is_annex, subclause (always present)
    - Numeric: clause_number, ancestors
    - Annex: collection, letter, ancestors
    """
    parts = clause.split(".")
    is_annex = parts[0][0].isalpha() and parts[0][0].isupper()
    depth = len(parts)

    result: dict[str, Any] = {"is_annex": is_annex, "subclause": clause}

    if is_annex:
        letter = parts[0]
        result["collection"] = f"Annex {letter}"
        result["letter"] = letter
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors
    else:
        result["clause_number"] = parts[0]
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors

    return result
