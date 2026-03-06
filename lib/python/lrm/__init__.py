"""Shared LRM parsing utilities."""

import re
from pathlib import Path


def load_lrm_titles(lrm_path: Path) -> dict[str, str]:
    """Build clause -> title map from an LRM text file.

    Handles three formats:
    - Subclauses: "4.1 General" or "A.8.1 Concatenations"
    - Top-level numeric: "4. Scheduling semantics"
    - Annex headers (multi-line): "Annex B\\n(normative)\\n\\nKeywords"
    """
    if not lrm_path.exists():
        return {}

    titles: dict[str, str] = {}
    lines = lrm_path.read_text(encoding="utf-8").splitlines()

    for i, line in enumerate(lines):
        m = re.match(r"^(\d+(?:\.\d+)+)\s+(.+)$", line)
        if m and m.group(1) not in titles:
            titles[m.group(1)] = m.group(2).strip()
            continue
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m and m.group(1) not in titles:
            titles[m.group(1)] = m.group(2).strip()
            continue

        m = re.match(r"^(\d+)\.\s+(.+)$", line)
        if m and m.group(1) not in titles:
            titles[m.group(1)] = m.group(2).strip()
            continue

        m = re.match(r"^Annex\s+([A-Z])$", line)
        if m:
            letter = m.group(1)
            normative = ""
            title = ""
            for j in range(i + 1, min(i + 6, len(lines))):
                nxt = lines[j].strip()
                if not nxt:
                    continue
                nm = re.match(r"^\((normative|informative)\)$", nxt)
                if nm:
                    normative = f"({nm.group(1)})"
                    continue
                title = nxt
                break
            if normative and title:
                titles[letter] = f"{normative} {title}"
            elif title:
                titles[letter] = title

    return titles


def _heading_depth(line: str) -> int | None:
    """Return the depth of a clause heading, or ``None``."""
    if re.match(r"^(\d+)\.\s+", line):
        return 1
    m = re.match(r"^(\d+(?:\.\d+)+)\s+", line)
    if m:
        return m.group(1).count(".") + 1
    if re.match(r"^Annex\s+[A-Z]$", line):
        return 1
    m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+", line)
    if m:
        return m.group(1).count(".") + 1
    return None


def _start_pattern(clause: str) -> re.Pattern[str]:
    """Return a regex matching the heading line for *clause*."""
    if re.match(r"^[A-Z]$", clause):
        return re.compile(rf"^Annex\s+{clause}$")
    if re.match(r"^\d+$", clause):
        return re.compile(rf"^{clause}\.\s+")
    return re.compile(rf"^{re.escape(clause)}\s+")


def extract_clause_text(lrm_path: Path, clause: str) -> str:
    """Return the full text of *clause*, from heading to next peer heading."""
    lines = lrm_path.read_text(encoding="utf-8").splitlines()
    depth = clause.count(".") + 1
    pat = _start_pattern(clause)

    start = None
    for i, line in enumerate(lines):
        if pat.match(line):
            start = i
            break
    if start is None:
        return ""

    end = len(lines)
    for i in range(start + 1, len(lines)):
        d = _heading_depth(lines[i])
        if d is not None and d <= depth:
            end = i
            break

    return "\n".join(lines[start:end]).rstrip()


FIGURE_LABEL_RE = re.compile(r"^Figure ([\d\w]+-[\d\w]+)")
TABLE_LABEL_RE = re.compile(r"^Table ([\d\w]+-[\d\w]+)")


def lrm_labels_for_subclause(
    lrm_path: Path, clause: str,
) -> tuple[list[str], list[str]]:
    """Find figure/table labels within a subclause's LRM text."""
    text = extract_clause_text(lrm_path, clause)
    figures: list[str] = []
    tables: list[str] = []
    for line in text.splitlines():
        m = FIGURE_LABEL_RE.match(line)
        if m:
            figures.append(m.group(1))
            continue
        m = TABLE_LABEL_RE.match(line)
        if m:
            tables.append(m.group(1))
    return figures, tables


def parse_subclauses(lrm_path: Path, clause: str) -> dict[str, str]:
    """Return direct subclauses of *clause* as a ``{number: title}`` dict."""
    all_titles = load_lrm_titles(lrm_path)
    prefix = clause + "."
    parent_dots = clause.count(".")
    return {
        k: v
        for k, v in all_titles.items()
        if k.startswith(prefix) and k.count(".") == parent_dots + 1
    }
