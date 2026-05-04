"""Walk the LRM and assemble per-subclause dependency records.

Each call to :func:`build_subclause_record` issues one read-only
dependency-list oracle call. The returned record carries just the
dependency identifiers in oracle order; downstream cycle detection and
ordering only consume that list.
"""

from typing import Any

from satisfy_subclause.oracles import compute_subclause_dependencies


def build_subclause_record(
    subclause: str, lrm: str, *, model: str,
) -> dict[str, Any]:
    """Return the dependency record for one subclause."""
    deps = compute_subclause_dependencies(subclause, lrm, model=model)
    return {"dependencies": deps}
