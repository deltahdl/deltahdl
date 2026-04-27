"""Batch driver: invoke ``satisfy_subclause`` for each subclause."""

from satisfy_subclause.pipeline import satisfy_subclause


def satisfy_subclauses(
    subclauses: list[str], lrm: str, *,
    model: str, labels: list[str],
) -> None:
    """Run ``satisfy_subclause`` for each entry in *subclauses*."""
    for subclause in subclauses:
        satisfy_subclause(subclause, lrm, model=model, labels=labels)
