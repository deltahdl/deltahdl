"""Batch driver: invoke ``satisfy_clause`` for each clause."""

from satisfy_clause.pipeline import satisfy_clause


def satisfy_clauses(
    clauses: list[str], lrm: str, *,
    model: str, labels: list[str],
) -> None:
    """Run ``satisfy_clause`` for each entry in *clauses*."""
    for clause in clauses:
        satisfy_clause(clause, lrm, model=model, labels=labels)
