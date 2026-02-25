"""Prompt handler for depth-2 clauses (e.g., '4.1', 'A.8')."""

from .common import build_hierarchy, build_top_level_line, format_prompt


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-2 clause."""
    h = build_hierarchy(clause)
    top = build_top_level_line(h, titles, lrm)
    hierarchy = (
        f"{top}\n"
        f"- Thoroughly understand {h['subclause']}"
        f" per LRM in {lrm}\n"
    )
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)
