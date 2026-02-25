"""Prompt handler for depth-5 clauses (e.g., '4.4.3.1.2', 'A.7.5.3.1')."""

from .common import build_hierarchy, format_prompt
from .prompt_v_w_x_y import _build_hierarchy_steps


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-5 clause."""
    h = build_hierarchy(clause)
    hierarchy = _build_hierarchy_steps(h, titles, lrm)
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)
