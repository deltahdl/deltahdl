"""Prompt handler for depth-3 clauses (e.g., '6.24.1', 'A.8.1')."""

from .common import build_hierarchy, build_top_level_line, format_prompt


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-3 clause."""
    h = build_hierarchy(clause)
    top = build_top_level_line(h, titles, lrm)

    if h["is_annex"]:
        hierarchy = (
            f"{top}\n"
            f"- Thoroughly understand {h['principles']}"
            f" per LRM in {lrm}\n"
            f"- Thoroughly understand {h['subclause']}"
            f" and how it fits within {h['principles']}"
            f" per LRM in {lrm}\n"
        )
    else:
        hierarchy = (
            f"{top}\n"
            f"- Thoroughly understand {h['principle']}"
            f" per LRM in {lrm}\n"
            f"- Thoroughly understand {h['subclause']}"
            f" and how it fits within {h['ancestors'][0]}"
            f" per LRM in {lrm}\n"
        )

    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)
