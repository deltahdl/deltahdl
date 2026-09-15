from typing import Any
from unittest.mock import patch


AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210),
    "A": (900, 939), "A.1": (900, 919),
}


RETRY_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210), "33.6.1": (900, 901),
}


def patched_oracle_sequence(*results: str) -> Any:
    return patch(
        "lib.python.lrm_subclause_dependencies.run_oracle_call",
        side_effect=list(results),
    )


def patched_toc(toc: dict[str, tuple[int, int]]) -> Any:
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value=toc,
    )


def patched_retry_toc() -> Any:
    return patched_toc(RETRY_AGGREGATE_TOC)
