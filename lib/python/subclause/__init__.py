"""Utilities for parsing and formatting LRM subclause numbers.

§1.5 of IEEE 1800-2023 organizes the standard into clauses and puts subclauses
within each clause to discuss individual constructs and concepts, so "11.4.11"
is a subclause and "11" is the clause holding it. The identifiers here take a
subclause of any depth, and ``build_hierarchy`` reports the clause it sits under
separately as ``clause_number``.
"""

from typing import Any


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
