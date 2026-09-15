import os
import re
from typing import Any, Iterator

from pypdf import PdfReader
from pypdf.errors import PyPdfError

from lib.python.subclause import build_hierarchy


_SUBCLAUSE_RE = re.compile(r"^([A-Z]|\d+)(\.\d+){0,4}\b")
_ANNEX_RE = re.compile(r"^Annex\s+([A-Z])\b")
_TOC_CACHE: dict[str, dict[str, tuple[int, int]]] = {}


def _walk_outline(items: Any) -> Iterator[Any]:
    for item in items:
        if isinstance(item, list):
            yield from _walk_outline(item)
        else:
            yield item


def _identifier_from_title(title: str) -> str | None:
    subclause_match = _SUBCLAUSE_RE.match(title)
    if subclause_match is not None:
        return subclause_match.group(0)
    annex_match = _ANNEX_RE.match(title)
    if annex_match is not None:
        return annex_match.group(1)
    return None


def _extract_entries(reader: PdfReader) -> list[tuple[str, int]]:
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
    result: dict[str, tuple[int, int]] = {}
    for i, (subclause, start) in enumerate(entries):
        end = total_pages
        prefix = subclause + "."
        for next_subclause, next_start in entries[i + 1:]:
            if not next_subclause.startswith(prefix):
                end = max(start, next_start - 1)
                break
        result[subclause] = (start, end)
    return result


def _has_numbered_subclauses(
    subclause: str, toc: dict[str, tuple[int, int]],
) -> bool:
    if subclause not in toc:
        return False
    prefix = subclause + "."
    return any(other.startswith(prefix) for other in toc)


def identifier_kind(
    identifier: str, toc: dict[str, tuple[int, int]],
) -> str | None:
    if identifier not in toc:
        return None
    if "." in identifier:
        return "subclause"
    if identifier[0].isdigit():
        return "clause"
    return "annex"


def is_top_level_aggregate(
    subclause: str, toc: dict[str, tuple[int, int]],
) -> bool:
    return "." not in subclause and _has_numbered_subclauses(subclause, toc)


def direct_numbered_children(
    subclause: str, toc: dict[str, tuple[int, int]],
) -> list[str]:
    prefix = subclause + "."
    return [
        other for other in toc
        if other.startswith(prefix) and "." not in other[len(prefix):]
    ]


def is_sub_level_parent(
    subclause: str, toc: dict[str, tuple[int, int]],
) -> bool:
    return "." in subclause and _has_numbered_subclauses(subclause, toc)


def load_toc(lrm_path: str) -> dict[str, tuple[int, int]]:
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


def _format_subclause(
    subclause: str,
    toc: dict[str, tuple[int, int]],
    *,
    truncate_at: str | None = None,
) -> str:
    if subclause not in toc:
        return f"§{subclause}"
    start, end = toc[subclause]
    if truncate_at is not None and truncate_at in toc:
        end = toc[truncate_at][0] - 1
    if end < start:
        return f"§{subclause}"
    if start == end:
        return f"§{subclause} (page {start})"
    return f"§{subclause} (pages {start}-{end})"


def build_lrm_read_instruction(subclause: str, lrm: str) -> str:
    h = build_hierarchy(subclause)
    toc = load_toc(lrm)
    page_hint = (
        " Use the Read tool with `pages: \"N\"`."
        " One page per call: the Read tool caps at 20 pages per request,"
        " and the content-filter budget is tighter still — single-page"
        " calls stay inside both."
    )
    target = _format_subclause(subclause, toc)
    if h["ancestors"]:
        chain = h["ancestors"] + [subclause]
        anc_strs = [
            _format_subclause(anc, toc, truncate_at=chain[i + 1])
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
