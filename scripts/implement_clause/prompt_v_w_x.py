"""Prompt handler for depth-3 clauses (e.g., '6.24.1', 'A.8.1')."""

from pathlib import Path

from .common import (
    build_hierarchy,
    build_supplementary_lines,
    invoke_claude,
    load_lrm_titles,
)


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    h = build_hierarchy(clause)

    if h["is_annex"]:
        subject = titles.get(h["letter"], "")
        hierarchy = (
            f"- Thoroughly understand that {h['collection']}"
            f" is about '{subject}' per LRM in {lrm}\n"
            f"- Thoroughly understand {h['principles']}"
            f" per LRM in {lrm}\n"
            f"- Thoroughly understand {h['subclause']}"
            f" and how it fits within {h['principles']}"
            f" per LRM in {lrm}\n"
        )
    else:
        title = titles.get(h["clause_number"], "")
        hierarchy = (
            f"- Thoroughly understand that Clause {h['clause_number']}"
            f" is about '{title}' per LRM in {lrm}\n"
            f"- Thoroughly understand {h['principle']}"
            f" per LRM in {lrm}\n"
            f"- Thoroughly understand {h['subclause']}"
            f" and how it fits within {h['ancestors'][0]}"
            f" per LRM in {lrm}\n"
        )

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
