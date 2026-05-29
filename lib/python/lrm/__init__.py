"""Helpers for reading the SystemVerilog LRM PDF."""

import os
import re
from typing import Any, Iterator

from pypdf import PdfReader
from pypdf.errors import PyPdfError

from lib.python.clause import build_hierarchy


_CLAUSE_RE = re.compile(r"^([A-Z]|\d+)(\.\d+){0,4}\b")
_ANNEX_RE = re.compile(r"^Annex\s+([A-Z])\b")
_TOC_CACHE: dict[str, dict[str, tuple[int, int]]] = {}


def _walk_outline(items: Any) -> Iterator[Any]:
    """Yield outline items in document order from a pypdf outline tree."""
    for item in items:
        if isinstance(item, list):
            yield from _walk_outline(item)
        else:
            yield item


def _identifier_from_title(title: str) -> str | None:
    """Return the clause identifier embedded in an outline title, or None.

    Numbered titles like ``23.2.1 Tasks`` and ``A.7 Foo`` resolve to
    ``23.2.1`` and ``A.7`` via the dotted-decimal regex. Annex headings
    like ``Annex B Keywords`` resolve to the single-letter identifier
    ``B`` so the annex appears in ``load_toc`` as a top-level entry on
    the same footing as numbered chapters.
    """
    clause_match = _CLAUSE_RE.match(title)
    if clause_match is not None:
        return clause_match.group(0)
    annex_match = _ANNEX_RE.match(title)
    if annex_match is not None:
        return annex_match.group(1)
    return None


def _extract_entries(reader: PdfReader) -> list[tuple[str, int]]:
    """Return ``[(clause, start_page)]`` from a PDF reader, in doc order."""
    entries: list[tuple[str, int]] = []
    for item in _walk_outline(reader.outline):
        title = str(item.title or "")
        identifier = _identifier_from_title(title)
        if identifier is None:
            continue
        page = reader.get_destination_page_number(item)
        if page is None:
            continue
        entries.append((identifier, page + 1))
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


def _has_numbered_subclauses(
    clause: str, toc: dict[str, tuple[int, int]],
) -> bool:
    """Return True iff ``clause`` is in ``toc`` and another TOC entry
    sits directly under it as ``clause.<digits>...``.
    """
    if clause not in toc:
        return False
    prefix = clause + "."
    return any(other.startswith(prefix) for other in toc)


def is_top_level_aggregate(
    clause: str, toc: dict[str, tuple[int, int]],
) -> bool:
    """Return True iff ``clause`` is a top-level entry that has at least
    one numbered subclause in ``toc``.

    Such clauses are aggregates: the enumeration root for a list of
    numbered subclauses, with no individual satisfaction work of their
    own. They are skipped by the walker and rejected as dependency-list
    entries. Top-level singletons like §2, §41, and Annex B remain
    non-aggregate and are walked as ordinary satisfaction units.
    """
    return "." not in clause and _has_numbered_subclauses(clause, toc)


def direct_numbered_children(
    clause: str, toc: dict[str, tuple[int, int]],
) -> list[str]:
    """Return ``clause``'s direct numbered children from ``toc`` in TOC order.

    A direct child is a TOC entry whose identifier is ``clause.<digits>``
    with no further dotted tail. The result preserves the TOC's
    iteration order so callers see entries in document order. Returns
    ``[]`` when ``clause`` has no numbered children — including when
    ``clause`` itself is absent from the TOC.
    """
    prefix = clause + "."
    return [
        other for other in toc
        if other.startswith(prefix) and "." not in other[len(prefix):]
    ]


def is_sub_level_parent(
    clause: str, toc: dict[str, tuple[int, int]],
) -> bool:
    """Return True iff ``clause`` is a sub-level entry that has at
    least one numbered subclause directly under it in ``toc``.

    A sub-level parent carries its own preamble rules and contains
    named numbered subclauses. The dependency oracle queries it for
    the deps of the preamble alone, since the named numbered subclauses
    are queried separately as their own targets.
    """
    return "." in clause and _has_numbered_subclauses(clause, toc)


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
