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
    payload = [{"number": 7, "title": "Satisfy IEEE 1800-2023 §3.1"}]
    assert _call(stub_completed, payload)[0] == payload


def test_list_open_issues_asks_only_for_open_issues(
    stub_completed: Callable[..., MagicMock],
) -> None:
    argv = _call(stub_completed, [])[1]
    assert argv[argv.index("--state") + 1] == "open"


def test_list_open_issues_passes_its_limit_to_gh(
    stub_completed: Callable[..., MagicMock],
) -> None:
    argv = _call(stub_completed, [], limit=7)[1]
    assert argv[argv.index("--limit") + 1] == "7"


def test_list_open_issues_reports_a_result_count_reaching_the_limit(
    capsys: pytest.CaptureFixture[str],
    stub_completed: Callable[..., MagicMock],
) -> None:
    _call(stub_completed, [{"number": 1, "title": "one"}], limit=1)
    assert "cut short" in capsys.readouterr().err


def test_list_open_issues_stays_quiet_below_the_limit(
    capsys: pytest.CaptureFixture[str],
    stub_completed: Callable[..., MagicMock],
) -> None:
    _call(stub_completed, [{"number": 1, "title": "one"}], limit=2)
    assert capsys.readouterr().err == ""


def _call_failing(
    stub_completed: Callable[..., MagicMock],
) -> pytest.ExceptionInfo[SystemExit]:
    with patch(
        "lib.python.github.subprocess.run",
        return_value=stub_completed(returncode=4, stderr="gh: auth required"),
    ), pytest.raises(SystemExit) as exit_info:
        list_open_issues()
    return exit_info


def test_list_open_issues_exits_with_the_code_gh_gave(
    stub_completed: Callable[..., MagicMock],
) -> None:
    assert _call_failing(stub_completed).value.code == 4


def test_list_open_issues_repeats_what_gh_said_on_failure(
    capsys: pytest.CaptureFixture[str],
    stub_completed: Callable[..., MagicMock],
) -> None:
    _call_failing(stub_completed)
    assert "gh: auth required" in capsys.readouterr().err
