"""Driver: enumerate a clause's descendants and delegate to satisfy_subclauses.

A clause with no descendants in the TOC is an error, not a silent
no-op — that condition means either the LRM PDF is wrong or the caller
named the wrong clause, and either way the right behaviour is to
surface the mismatch.
"""

import sys

from satisfy_subclauses.pipeline import satisfy_subclauses

from lib.python.lrm import load_toc


def descendants_of(
    clause: str, toc: dict[str, tuple[int, int]],
) -> list[str]:
    """Return descendants of ``clause`` from ``toc`` in document order.

    Keys are sorted segment-by-segment as integers so ``33.10`` follows
    ``33.9`` instead of preceding it lexicographically.
    """
    prefix = f"{clause}."
    return sorted(
        (k for k in toc if k.startswith(prefix)),
        key=lambda k: tuple(int(s) for s in k.split(".")[1:]),
    )


def satisfy_clause(
    clause: str, lrm: str, *, model: str, labels: list[str],
) -> None:
    """Enumerate §``clause``'s descendants and delegate to satisfy_subclauses."""
    toc = load_toc(lrm)
    descendants = descendants_of(clause, toc)
    if not descendants:
        sys.exit(
            f"satisfy_clause: §{clause} has no descendants in the TOC"
            f" loaded from {lrm}. Check that --lrm names the correct PDF."
        )
    satisfy_subclauses(descendants, lrm, model=model, labels=labels)
