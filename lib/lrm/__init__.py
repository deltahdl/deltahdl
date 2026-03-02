"""Shared LRM parsing utilities."""

import re
from pathlib import Path


def _load_all_titles(lrm_path: Path) -> dict[str, str]:
    """Build clause -> title map from an LRM text file."""
    titles: dict[str, str] = {}
    lines = lrm_path.read_text(encoding="utf-8").splitlines()

    for line in lines:
        m = re.match(r"^(\d+(?:\.\d+)+)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()

    return titles


def parse_subclauses(lrm_path: Path, clause: str) -> dict[str, str]:
    """Return direct subclauses of *clause* as a ``{number: title}`` dict."""
    all_titles = _load_all_titles(lrm_path)
    prefix = clause + "."
    parent_dots = clause.count(".")
    return {
        k: v
        for k, v in all_titles.items()
        if k.startswith(prefix) and k.count(".") == parent_dots + 1
    }
