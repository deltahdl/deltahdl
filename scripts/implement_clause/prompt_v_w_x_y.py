"""Prompt handler for depth-4 clauses (e.g., '4.4.3.1', 'A.7.5.3')."""

from .common import build_hierarchy, build_top_level_line, format_prompt


def _build_hierarchy_steps(h: dict, titles: dict, lrm: str) -> str:
    """Build the 'Thoroughly understand' hierarchy lines."""
    lines = [build_top_level_line(h, titles, lrm)]

    root = h["principles"] if h["is_annex"] else h["principle"]
    lines.append(
        f"- Thoroughly understand {root}"
        f" per LRM in {lrm}",
    )
    parent = root
    for ancestor in h["ancestors"]:
        lines.append(
            f"- Thoroughly understand {ancestor}"
            f" and how it fits within {parent}"
            f" per LRM in {lrm}",
        )
        parent = ancestor
    lines.append(
        f"- Thoroughly understand {h['subclause']}"
        f" and how it fits within {parent}"
        f" per LRM in {lrm}",
    )

    return "\n".join(lines) + "\n"


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-4 clause."""
    h = build_hierarchy(clause)
    hierarchy = _build_hierarchy_steps(h, titles, lrm)
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)
