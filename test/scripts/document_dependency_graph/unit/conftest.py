"""Shared fixtures for document_dependency_graph unit tests."""

from typing import Any
from unittest.mock import patch

import pytest

import document_dependency_graph


_DEFAULT_TOC: dict[str, tuple[int, int]] = {"4.4": (10, 20)}
_DEFAULT_RECORD: dict[str, Any] = {
    "dependencies": [],
    "proofs": {},
    "prerequisites": {},
}


@pytest.fixture()
def run_main(make_lrm, make_output):
    """Patch the walk hooks, run main(), and return the mock pair.

    The mocks (load_toc, build_subclause_record) are returned so each
    test can assert on call counts/args without re-stating the boiler
    plate of patching, building argv, and invoking main().
    """

    def _run(*, toc=None, record=None, extra_argv=None):
        toc_payload = _DEFAULT_TOC if toc is None else toc
        record_payload = _DEFAULT_RECORD if record is None else record
        argv = [
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ]
        if extra_argv:
            argv.extend(extra_argv)
        toc_patch = patch(
            "document_dependency_graph.load_toc",
            return_value=toc_payload,
        )
        record_patch = patch(
            "document_dependency_graph.build_subclause_record",
            return_value=record_payload,
        )
        with toc_patch as mock_toc, record_patch as mock_record:
            document_dependency_graph.main(argv)
        return mock_toc, mock_record

    return _run
