"""Helpers for reading the SystemVerilog LRM PDF."""

import os
import re
from typing import Any, Iterator

from pypdf import PdfReader
from pypdf.errors import PyPdfError

from lib.python.clause import build_hierarchy


_CLAUSE_RE = re.compile(r"^([A-Z]|\d+)(\.\d+){0,4}\b")
_TOC_CACHE: dict[str, dict[str, tuple[int, int]]] = {}


def _walk_outline(items: Any) -> Iterator[Any]:
    """Yield outline items in document order from a pypdf outline tree."""
    for item in items:
        if isinstance(item, list):
            yield from _walk_outline(item)
        else:
            yield item


def _extract_entries(reader: PdfReader) -> list[tuple[str, int]]:
    """Return ``[(clause, start_page)]`` from a PDF reader, in doc order."""
    entries: list[tuple[str, int]] = []
    for item in _walk_outline(reader.outline):
        title = str(item.title or "")
        match = _CLAUSE_RE.match(title)
        if match is None:
            continue
        page = reader.get_destination_page_number(item)
        if page is None:
            continue
        entries.append((match.group(0), page + 1))
    return entries


def _compute_ranges(
    entries: list[tuple[str, int]], total_pages: int,
) -> dict[str, tuple[int, int]]:
    """Compute ``{clause: (start, end)}`` from ordered ``entries``."""
    result: dict[str, tuple[int, int]] = {}
    for i, (clause, start) in enumerate(entries):
        end = total_pages
        prefix = clause + "."
        for next_clause, next_start in entries[i + 1:]:
            if not next_clause.startswith(prefix):
                end = max(start, next_start - 1)
                break
        result[clause] = (start, end)
    return result


def load_toc(lrm_path: str) -> dict[str, tuple[int, int]]:
    """Return a mapping of clause → (start_page, end_page) for ``lrm_path``.

    Pages are 1-indexed. Returns ``{}`` for any unreadable PDF or empty
    outline. Memoized in-process by absolute path.
    """
    key = os.path.abspath(lrm_path)
    if key in _TOC_CACHE:
        return _TOC_CACHE[key]
    try:
        reader = PdfReader(key)
        entries = _extract_entries(reader)
        toc = _compute_ranges(entries, len(reader.pages))
    except (OSError, PyPdfError):
        toc = {}
    _TOC_CACHE[key] = toc
    return toc


def _format_clause(
    clause: str,
    toc: dict[str, tuple[int, int]],
    *,
    truncate_at: str | None = None,
) -> str:
    """Return ``§clause`` with an optional ``(pages A-B)`` suffix.

    When ``truncate_at`` names another clause present in ``toc``, the
    end page is clamped to ``toc[truncate_at].start - 1`` so an
    ancestor's range does not overlap the descendant being read
    separately.
    """
    if clause not in toc:
        return f"§{clause}"
    start, end = toc[clause]
    if truncate_at is not None and truncate_at in toc:
        end = toc[truncate_at][0] - 1
    if end < start:
        return f"§{clause}"
    if start == end:
        return f"§{clause} (page {start})"
    return f"§{clause} (pages {start}-{end})"


def build_lrm_read_instruction(subclause: str, lrm: str) -> str:
    """Build an instruction to read the relevant LRM sections."""
    h = build_hierarchy(subclause)
    toc = load_toc(lrm)
    page_hint = (
        " Use the Read tool with `pages: \"N\"`."
        " One page per call: the Read tool caps at 20 pages per request,"
        " and the content-filter budget is tighter still — single-page"
        " calls stay inside both."
    )
    target = _format_clause(subclause, toc)
    if h["ancestors"]:
        chain = h["ancestors"] + [subclause]
        anc_strs = [
            _format_clause(anc, toc, truncate_at=chain[i + 1])
            for i, anc in enumerate(h["ancestors"])
        ]
        ancestors_str = ", ".join(anc_strs)
        return (
            f"Read {target} and its ancestor subclauses"
            f" ({ancestors_str}) in the LRM at {lrm}."
            " Also read any General or Overview subclauses"
            " at each level."
            + page_hint
        )
    parts = subclause.split(".")
    is_general = len(parts) == 2 and parts[1] == "1"
    instruction = f"Read {target} in the LRM at {lrm}."
    if not is_general:
        instruction += (
            " Also read any General or Overview subclauses"
            " for context."
        )
    return instruction + page_hint
