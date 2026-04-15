"""Helpers for reading the SystemVerilog LRM PDF."""

from lib.python.clause import build_hierarchy


def build_lrm_read_instruction(subclause: str, lrm: str) -> str:
    """Build an instruction to read the relevant LRM sections."""
    h = build_hierarchy(subclause)
    page_hint = (
        " When reading the PDF, read one page at a time"
        " (never request more than 2 pages per Read call)"
        " to avoid content filtering errors."
    )
    if h["ancestors"]:
        ancestors_str = ", ".join(f"§{a}" for a in h["ancestors"])
        return (
            f"Read §{subclause} and its ancestor subclauses"
            f" ({ancestors_str}) in the LRM at {lrm}."
            " Also read any General or Overview subclauses"
            " at each level."
            + page_hint
        )
    parts = subclause.split(".")
    is_general = len(parts) == 2 and parts[1] == "1"
    instruction = f"Read §{subclause} in the LRM at {lrm}."
    if not is_general:
        instruction += (
            " Also read any General or Overview subclauses"
            " for context."
        )
    return instruction + page_hint
