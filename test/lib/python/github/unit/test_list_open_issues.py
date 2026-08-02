"""Unit tests for lib.python.github.list_open_issues.

A caller of this function decides something against the whole open set,
so the hazard is not a wrong query but a short answer: ``gh issue list``
caps its results, and a listing cut off at the cap looks exactly like a
repository holding that many issues. These pin the state selector, the
limit reaching gh, and the report that a result count touching the limit
is suspected truncation.
"""

import json
from collections.abc import Callable
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from lib.python.github import list_open_issues


def _call(
    stub_completed: Callable[..., MagicMock],
    payload: list[dict[str, Any]],
    **kwargs: int,
) -> tuple[list[dict[str, Any]], list[str]]:
    """Run list_open_issues against a stubbed gh; return its answer and argv."""
    with patch(
        "lib.python.github.subprocess.run",
        return_value=stub_completed(stdout=json.dumps(payload)),
    ) as mock_run:
        issues = list_open_issues(**kwargs)
    argv: list[str] = mock_run.call_args_list[0][0][0]
    return issues, argv


def test_list_open_issues_returns_the_listed_issues(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """The payload gh printed is what the caller gets back."""
    payload = [{"number": 7, "title": "Satisfy IEEE 1800-2023 §3.1"}]
    assert _call(stub_completed, payload)[0] == payload


def test_list_open_issues_asks_only_for_open_issues(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """The state selector is open, so closed work is not listed."""
    argv = _call(stub_completed, [])[1]
    assert argv[argv.index("--state") + 1] == "open"


def test_list_open_issues_passes_its_limit_to_gh(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A caller raising the limit raises the one gh is given."""
    argv = _call(stub_completed, [], limit=7)[1]
    assert argv[argv.index("--limit") + 1] == "7"


def test_list_open_issues_reports_a_result_count_reaching_the_limit(
    capsys: pytest.CaptureFixture[str],
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A full result set is announced as the suspected truncation it is."""
    _call(stub_completed, [{"number": 1, "title": "one"}], limit=1)
    assert "cut short" in capsys.readouterr().err


def test_list_open_issues_stays_quiet_below_the_limit(
    capsys: pytest.CaptureFixture[str],
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A listing that did not reach the limit is reported without comment."""
    _call(stub_completed, [{"number": 1, "title": "one"}], limit=2)
    assert capsys.readouterr().err == ""
