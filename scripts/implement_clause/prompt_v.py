"""Prompt handler for depth-1 clauses (e.g., '4', 'B')."""

from .common import build_hierarchy, build_top_level_line, format_prompt


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-1 clause."""
    h = build_hierarchy(clause)
    top = build_top_level_line(h, titles, lrm)
    hierarchy = f"{top}\n"
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)
