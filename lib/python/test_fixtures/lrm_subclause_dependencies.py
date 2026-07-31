"""Shared TOC fixtures and oracle-patch helpers for lrm_subclause_dependencies tests."""

from typing import Any
from unittest.mock import patch


AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210),
    "A": (900, 939), "A.1": (900, 919),
}


# "33.6.1" is the corrected answer the retry tests hand back after the
# aggregate "8" is turned down. It is listed here so those tests reach
# the aggregate branch they are about, rather than being turned down a
# second time for naming a section this table does not hold.
RETRY_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210), "33.6.1": (900, 901),
}


def patched_oracle_sequence(*results: str) -> Any:
    """Patch run_oracle_call so each invocation returns the next *results* item."""
    return patch(
        "lib.python.lrm_subclause_dependencies.run_oracle_call",
        side_effect=list(results),
    )


def patched_toc(toc: dict[str, tuple[int, int]]) -> Any:
    """Patch load_toc so oracle answers are judged against *toc*."""
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value=toc,
    )


def patched_retry_toc() -> Any:
    """Patch load_toc so the aggregate-rejection branch fires on '["8"]'."""
    return patched_toc(RETRY_AGGREGATE_TOC)
