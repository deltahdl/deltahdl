"""Utilities for parsing and formatting LRM subclause numbers.

§1.5 of IEEE 1800-2023 organizes the standard into clauses and puts subclauses
within each clause to discuss individual constructs and concepts, so "11.4.11"
is a subclause and "11" is the clause holding it. The identifiers here take a
subclause of any depth, and ``build_hierarchy`` reports the clause it sits under
separately as ``clause_number``.
"""

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


def subclause_to_filename(prefix: str, subclause: str) -> str:
    """Convert prefix + subclause to a target filename (without .cpp)."""
    if subclause.startswith("non-lrm"):
        topic = subclause.split(":", 1)[1] if ":" in subclause else "misc"
        return f"test_non_lrm_{topic}"
    prefix = prefix.rstrip("_")
    if re.match(r"^[A-Z]$", subclause):
        return f"{prefix}_annex_{subclause.lower()}"
    annex_match = re.match(r"^([A-Z])\.(.+)$", subclause)
    if annex_match:
        letter = annex_match.group(1).lower()
        parts = annex_match.group(2).split(".")
        padded = "_".join(p.zfill(2) for p in parts)
        return f"{prefix}_annex_{letter}_{padded}"
    parts = subclause.split(".")
    padded = "_".join(p.zfill(2) for p in parts)
    return f"{prefix}_subclause_{padded}"


def build_hierarchy(subclause: str) -> dict[str, Any]:
    """Derive template variables from a subclause string.

    Returns a dict with keys:
    - is_annex, subclause (always present)
    - Numeric: clause_number, ancestors
    - Annex: collection, letter, ancestors
    """
    parts = subclause.split(".")
    is_annex = parts[0][0].isalpha() and parts[0][0].isupper()
    depth = len(parts)

    result: dict[str, Any] = {"is_annex": is_annex, "subclause": subclause}

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
