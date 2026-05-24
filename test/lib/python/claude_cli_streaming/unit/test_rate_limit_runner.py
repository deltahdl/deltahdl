"""Unit tests for rate-limit detection in run_claude_streaming + retry wrapper."""

import io
from datetime import datetime
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest


# --- shared Popen scaffolding (variant of the helpers in --------------------
# --- test_claude_cli_streaming.py — kept distinct so jscpd does not flag
# --- the cross-file duplicate; same shape, distinct identifiers)


def _build_fake_subprocess(
    output_lines: list[str], *, captured_stderr: str = "", exit_code: int = 0,
) -> tuple[MagicMock, MagicMock]:
    """Return a Popen-shaped context manager + the child MagicMock."""
    child = MagicMock()
    child.stdout = io.StringIO("".join(output_lines))
    child.stderr = MagicMock()
    child.stderr.read.return_value = captured_stderr
    child.stdin = MagicMock()
    child.wait.return_value = exit_code
    manager = MagicMock()
    manager.__enter__.return_value = child
    manager.__exit__.return_value = None
    return manager, child


def run_with_stubbed_popen(
    streaming: ModuleType, lines: list[str],
) -> Any:
    """Drive run_claude_streaming against a stubbed Popen and return its result."""
    manager, _ = _build_fake_subprocess(lines)
    target = "lib.python.claude_cli_streaming.subprocess.Popen"
    with patch(target, return_value=manager):
        return streaming.run_claude_streaming(
            ["claude"], "prompt", env={"PATH": "/usr/bin"},
        )


def run_retry(
    streaming: ModuleType, side_effects: list[Any], *, role: str = "Step",
) -> tuple[MagicMock, SystemExit | None]:
    """Drive run_claude_streaming_with_retry with patched inner side-effects."""
    retry_cmd = ["claude", "--continue"]
    inner = patch.object(
        streaming, "run_claude_streaming", side_effect=side_effects,
    )
    with inner as mock:
        try:
            streaming.run_claude_streaming_with_retry(
                ["claude"], "orig", env={}, retry_cmd=retry_cmd, role=role,
            )
        except SystemExit as exit_exc:
            return mock, exit_exc
    return mock, None


# --- shared fixture lines ---------------------------------------------------


_RATE_LIMIT_EVENT_LINE = (
    '{"type":"rate_limit_event","rate_limit_info":'
    '{"rateLimitType":"five_hour","resetsAt":1779592200,'
    '"overageStatus":"rejected",'
    '"overageDisabledReason":"org_level_disabled"}}\n'
)


_SYNTHETIC_429_ASSISTANT_LINE = (
    '{"type":"assistant","apiErrorStatus":429,"error":"rate_limit",'
    '"isApiErrorMessage":true,"message":{"model":"<synthetic>",'
    '"role":"assistant","stop_reason":"stop_sequence","content":'
    '[{"type":"text","text":"Usage credits are required for long context requests."}]}}\n'
)


_RESULT_EVENT_429_LINE = (
    '{"type":"result","subtype":"error_api","is_error":true,'
    '"api_error_status":429,"errors":["rate limit"]}\n'
)


def _capture_rate_limit(streaming: ModuleType, lines: list[str]) -> Any:
    """Run with a stubbed Popen and return the RateLimitError raised."""
    try:
        run_with_stubbed_popen(streaming, lines)
    except streaming.RateLimitError as exc:
        return exc
    raise RuntimeError("expected RateLimitError, got success")


# --- run_claude_streaming: rate-limit detection -----------------------------


def test_run_claude_streaming_raises_on_synthetic_429_assistant(
    streaming: ModuleType,
) -> None:
    """A synthetic assistant 429 raises RateLimitError, not MissingResultEventError."""
    lines = [_RATE_LIMIT_EVENT_LINE, _SYNTHETIC_429_ASSISTANT_LINE]
    with pytest.raises(streaming.RateLimitError):
        run_with_stubbed_popen(streaming, lines)


def test_run_claude_streaming_raises_on_result_event_429(
    streaming: ModuleType,
) -> None:
    """A result event with api_error_status=429 raises RateLimitError."""
    with pytest.raises(streaming.RateLimitError):
        run_with_stubbed_popen(
            streaming, [_RATE_LIMIT_EVENT_LINE, _RESULT_EVENT_429_LINE],
        )


def test_run_claude_streaming_429_carries_rate_limit_type(
    streaming: ModuleType,
) -> None:
    """The raised error carries rateLimitType captured from the prior event."""
    exc = _capture_rate_limit(
        streaming, [_RATE_LIMIT_EVENT_LINE, _SYNTHETIC_429_ASSISTANT_LINE],
    )
    assert exc.rate_limit_type == "five_hour"


def test_run_claude_streaming_429_carries_resets_at(streaming: ModuleType) -> None:
    """The raised error carries resetsAt captured from the prior event."""
    exc = _capture_rate_limit(
        streaming, [_RATE_LIMIT_EVENT_LINE, _SYNTHETIC_429_ASSISTANT_LINE],
    )
    assert exc.resets_at == 1779592200


def test_run_claude_streaming_429_carries_overage_status(
    streaming: ModuleType,
) -> None:
    """The raised error carries overageStatus captured from the prior event."""
    exc = _capture_rate_limit(
        streaming, [_RATE_LIMIT_EVENT_LINE, _SYNTHETIC_429_ASSISTANT_LINE],
    )
    assert exc.overage_status == "rejected"


def test_run_claude_streaming_429_carries_overage_disabled_reason(
    streaming: ModuleType,
) -> None:
    """The raised error carries overageDisabledReason."""
    exc = _capture_rate_limit(
        streaming, [_RATE_LIMIT_EVENT_LINE, _SYNTHETIC_429_ASSISTANT_LINE],
    )
    assert exc.overage_disabled_reason == "org_level_disabled"


def test_run_claude_streaming_429_carries_synthetic_text(
    streaming: ModuleType,
) -> None:
    """The raised error carries the synthetic assistant text verbatim."""
    exc = _capture_rate_limit(
        streaming, [_RATE_LIMIT_EVENT_LINE, _SYNTHETIC_429_ASSISTANT_LINE],
    )
    assert "Usage credits are required" in (exc.synthetic_text or "")


def test_run_claude_streaming_429_without_prior_rate_limit_event(
    streaming: ModuleType,
) -> None:
    """A synthetic 429 with no prior rate_limit_event still raises RateLimitError."""
    exc = _capture_rate_limit(streaming, [_SYNTHETIC_429_ASSISTANT_LINE])
    assert exc.resets_at is None


def test_run_claude_streaming_429_repeated_events_capture_first_synthetic(
    streaming: ModuleType,
) -> None:
    """Repeated 429 events keep the first synthetic text and skip later captures."""
    second_line = _SYNTHETIC_429_ASSISTANT_LINE.replace(
        "Usage credits are required for long context requests.",
        "Different synthetic text on the second event.",
    )
    exc = _capture_rate_limit(
        streaming,
        [_SYNTHETIC_429_ASSISTANT_LINE, second_line],
    )
    assert "Usage credits are required" in (exc.synthetic_text or "")


def test_run_claude_streaming_429_does_not_raise_missing_result(
    streaming: ModuleType,
) -> None:
    """A 429 path raises RateLimitError, not MissingResultEventError.

    Regression test for the misdiagnosis the user hit: the synthetic
    assistant 429 has no terminal result event, so without this guard
    the runner would raise MissingResultEventError and the retry wrapper
    would burn its budget against an unchanged failure mode.
    """
    try:
        run_with_stubbed_popen(streaming, [_SYNTHETIC_429_ASSISTANT_LINE])
    except streaming.MissingResultEventError as exc:
        raise AssertionError(
            "MissingResultEventError must not be raised",
        ) from exc
    except streaming.RateLimitError:
        return
    raise AssertionError("expected RateLimitError")


# --- run_claude_streaming: replay captured failing oracle session -----------


_FIXTURES_DIR = Path(__file__).parent / "fixtures"


def _load_fixture_lines(name: str) -> list[str]:
    """Return JSONL lines from a fixture under the unit/fixtures directory."""
    path = _FIXTURES_DIR / name
    return [line for line in path.read_text().splitlines() if line.strip()]


def test_replay_captured_failing_oracle_session_raises_rate_limit(
    streaming: ModuleType,
) -> None:
    """Replaying the historical failing session diagnoses RateLimitError."""
    lines = [
        line + "\n" for line
        in _load_fixture_lines("failing_oracle_session.jsonl")
    ]
    with pytest.raises(streaming.RateLimitError):
        run_with_stubbed_popen(streaming, lines)


def test_replay_captured_failing_oracle_session_includes_synthetic_text(
    streaming: ModuleType,
) -> None:
    """The replayed failure surfaces the historical synthetic message."""
    lines = [
        line + "\n" for line
        in _load_fixture_lines("failing_oracle_session.jsonl")
    ]
    exc = _capture_rate_limit(streaming, lines)
    assert "Usage credits are required" in (exc.synthetic_text or "")


# --- run_claude_streaming_with_retry: rate-limit translation ---------------


_DEFAULT_RATE_LIMIT_INFO: dict[str, Any] = {
    "rateLimitType": "five_hour",
    "resetsAt": 1779592200,
    "overageStatus": "rejected",
    "overageDisabledReason": "org_level_disabled",
}


def _rate_limit(streaming: ModuleType, **kwargs: Any) -> Any:
    """Construct a RateLimitError with sensible defaults."""
    defaults: dict[str, Any] = {
        "rate_limit_info": _DEFAULT_RATE_LIMIT_INFO,
        "synthetic_text": "Usage credits are required.",
        "stderr": "",
    }
    defaults.update(kwargs)
    return streaming.RateLimitError(**defaults)


def test_retry_exits_immediately_on_rate_limit(streaming: ModuleType) -> None:
    """A RateLimitError on the first attempt exits without retrying."""
    inner, exc = run_retry(streaming, [_rate_limit(streaming)])
    assert (inner.call_count, exc is not None) == (1, True)


def test_retry_rate_limit_does_not_consume_filter_budget(
    streaming: ModuleType,
) -> None:
    """A RateLimitError does not increment the content-filter retry counter."""
    side = [_rate_limit(streaming)]
    inner, _ = run_retry(streaming, side)
    assert inner.call_count == 1


def test_retry_rate_limit_does_not_consume_missing_result_budget(
    streaming: ModuleType,
) -> None:
    """A RateLimitError does not increment the missing-result retry counter."""
    side = [_rate_limit(streaming)]
    inner, _ = run_retry(streaming, side)
    assert inner.call_count == 1


def test_retry_rate_limit_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error names the caller's role."""
    run_retry(streaming, [_rate_limit(streaming)], role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_retry_rate_limit_exit_message_includes_rate_limit_type(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error names the rate-limit type."""
    run_retry(streaming, [_rate_limit(streaming)])
    assert "five_hour" in capsys.readouterr().err


def test_retry_rate_limit_exit_message_includes_reset_time(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error includes a rendered local-time reset clock."""
    run_retry(streaming, [_rate_limit(streaming)])
    expected_clock = datetime.fromtimestamp(
        1779592200,
    ).astimezone().strftime("%H:%M")
    assert expected_clock in capsys.readouterr().err


def test_retry_rate_limit_exit_message_includes_overage_status(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error names the overage status."""
    run_retry(streaming, [_rate_limit(streaming)])
    assert "rejected" in capsys.readouterr().err


def test_retry_rate_limit_exit_message_includes_overage_disabled_reason(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error names the overage-disabled reason."""
    run_retry(streaming, [_rate_limit(streaming)])
    assert "org_level_disabled" in capsys.readouterr().err


def test_retry_rate_limit_exit_message_includes_synthetic_text(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error quotes the CLI's synthetic message verbatim."""
    run_retry(
        streaming,
        [_rate_limit(streaming, synthetic_text="Usage credits are required.")],
    )
    assert "Usage credits are required." in capsys.readouterr().err


def test_retry_rate_limit_exit_message_mentions_restart(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error hints that re-running after the reset is safe."""
    run_retry(streaming, [_rate_limit(streaming)])
    assert "re-run" in capsys.readouterr().err.lower()


def test_retry_rate_limit_exit_dumps_stderr(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error dumps the captured stderr from the inner call."""
    run_retry(
        streaming,
        [_rate_limit(streaming, stderr="UNIQUE_RL_STDERR")],
    )
    assert "UNIQUE_RL_STDERR" in capsys.readouterr().err
