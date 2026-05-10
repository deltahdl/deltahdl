"""Walk the LRM and assemble per-subclause dependency records.

Each call to :func:`build_subclause_record` issues one read-only
dependency-list oracle call. The returned record carries just the
dependency identifiers in oracle order, restricted to leaves of the
LRM table of contents. Aggregate parent-clause identifiers (e.g. a
chapter id like ``11`` instead of a leaf like ``11.4.13``) are
filtered out because the prompt asks for leaves; an aggregate
slipping through would create cross-chapter cycles in the
condensation downstream.
"""

from typing import Any

from satisfy_subclause.oracles import compute_subclause_dependencies


def build_subclause_record(
    subclause: str, lrm: str, *, model: str, effort: str, leaves: set[str],
) -> dict[str, Any]:
    """Return the dependency record for one subclause."""
    deps = compute_subclause_dependencies(
        subclause, lrm, model=model, effort=effort,
    )
    return {"dependencies": [d for d in deps if d in leaves]}
