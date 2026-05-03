"""Walk the LRM and assemble per-subclause dependency records.

Each call to :func:`build_subclause_record` issues one dependency-list
oracle call followed by one proof-sentence and one prerequisites
oracle call per dependency. Splitting the questions keeps every Claude
invocation single-purpose.
"""

from satisfy_subclause.oracles import compute_subclause_dependencies

from .oracles import compute_prerequisites, compute_proof_sentence


def build_subclause_record(
    subclause: str, lrm: str, *, model: str,
) -> dict:
    """Return the rich dependency record for one subclause.

    The record carries the dependency identifiers in oracle order
    plus, keyed by dependency, the proof sentence quoted from
    §subclause and what §subclause needs §dep to already provide.
    """
    deps = compute_subclause_dependencies(subclause, lrm, model=model)
    proofs = {
        dep: compute_proof_sentence(subclause, dep, lrm, model=model)
        for dep in deps
    }
    prerequisites = {
        dep: compute_prerequisites(subclause, dep, lrm, model=model)
        for dep in deps
    }
    return {
        "dependencies": deps,
        "proofs": proofs,
        "prerequisites": prerequisites,
    }
