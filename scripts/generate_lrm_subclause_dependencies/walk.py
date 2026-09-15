from typing import Any

from lib.python.lrm_subclause_dependencies import compute_subclause_dependencies


def build_subclause_record(
    subclause: str, lrm: str, *, model: str, effort: str,
) -> dict[str, Any]:
    deps = compute_subclause_dependencies(
        subclause, lrm, model=model, effort=effort,
    )
    return {"dependencies": deps}
