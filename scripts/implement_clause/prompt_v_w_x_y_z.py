"""Prompt handler for depth-5 clauses (e.g., '4.4.3.1.2', 'A.7.5.3.1')."""

from pathlib import Path

from .common import (
    build_hierarchy,
    build_supplementary_lines,
    invoke_claude,
    load_lrm_titles,
)

# Reuse the generic hierarchy builder from depth-4 — it handles any depth.
from .prompt_v_w_x_y import _build_hierarchy_steps


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    h = build_hierarchy(clause)
    hierarchy = _build_hierarchy_steps(h, titles, lrm)

    return (
        "Create and execute a Claude task list."
        " Each task must be blocked by the preceding task.\n\n"
        f"{hierarchy}"
        f"{supplementary}"
        f"- Implement ALL aspects (not just parsing) of"
        f" {h['subclause']} per LRM in {lrm}"
        f" through test-driven development unit tests\n"
        f"- Prove that the unit tests cover ALL aspects of"
        f" {h['subclause']} per LRM in {lrm} not just parsing\n"
        f"- Prove that the implementation covers ALL aspects of"
        f" {h['subclause']} per LRM in {lrm} not just parsing\n"
        f"- Read all of Issue {issue}\n"
        f"- Correct Issue {issue}\n"
    )


def run(lrm_path: Path, clause: str, *, issue: int, model: str) -> None:
    titles = load_lrm_titles(lrm_path)
    supplementary = build_supplementary_lines(clause)
    if supplementary:
        supplementary += "\n"
    prompt = build_prompt(
        clause, titles, str(lrm_path),
        issue=issue, supplementary=supplementary,
    )
    invoke_claude(prompt, model=model)
