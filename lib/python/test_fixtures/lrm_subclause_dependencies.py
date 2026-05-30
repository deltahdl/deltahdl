"""Shared TOC fixtures and oracle-patch helpers for lrm_subclause_dependencies tests."""

from typing import Any
from unittest.mock import patch


AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210),
    "A": (900, 939), "A.1": (900, 919),
}


RETRY_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210),
}


def patched_oracle_sequence(*results: str) -> Any:
    """Patch run_oracle_call so each invocation returns the next *results* item."""
    return patch(
        "lib.python.lrm_subclause_dependencies.run_oracle_call",
        side_effect=list(results),
    )


def patched_retry_toc() -> Any:
    """Patch load_toc so the aggregate-rejection branch fires on '["8"]'."""
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=RETRY_AGGREGATE_TOC,
    )
