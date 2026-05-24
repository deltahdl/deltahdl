"""Unit tests for format_resets_at in lib.python.claude_cli_streaming."""

from datetime import datetime, timezone
from types import ModuleType


_RESETS_AT_EPOCH = 1779592200  # 2026-05-24 03:10:00 UTC


def _at(epoch: int) -> datetime:
    """Return *epoch* as a timezone-aware UTC datetime."""
    return datetime.fromtimestamp(epoch, tz=timezone.utc)


def test_format_resets_at_returns_unknown_for_none(streaming: ModuleType) -> None:
    """A None resets_at renders as 'unknown'."""
    assert streaming.format_resets_at(None, _at(_RESETS_AT_EPOCH)) == "unknown"


def test_format_resets_at_includes_local_time_date(streaming: ModuleType) -> None:
    """The rendered string includes the local-time date prefix."""
    now = _at(_RESETS_AT_EPOCH - 3600)
    rendered = streaming.format_resets_at(_RESETS_AT_EPOCH, now)
    expected = datetime.fromtimestamp(
        _RESETS_AT_EPOCH,
    ).astimezone().strftime("%Y-%m-%d")
    assert expected in rendered


def test_format_resets_at_includes_local_time_clock(streaming: ModuleType) -> None:
    """The rendered string includes the local-time HH:MM clock."""
    now = _at(_RESETS_AT_EPOCH - 3600)
    rendered = streaming.format_resets_at(_RESETS_AT_EPOCH, now)
    expected = datetime.fromtimestamp(
        _RESETS_AT_EPOCH,
    ).astimezone().strftime("%H:%M")
    assert expected in rendered


def test_format_resets_at_includes_timezone_abbreviation(
    streaming: ModuleType,
) -> None:
    """The rendered string includes the local timezone abbreviation."""
    now = _at(_RESETS_AT_EPOCH - 3600)
    rendered = streaming.format_resets_at(_RESETS_AT_EPOCH, now)
    expected = datetime.fromtimestamp(
        _RESETS_AT_EPOCH,
    ).astimezone().strftime("%Z")
    assert expected in rendered


def test_format_resets_at_includes_delta_under_one_hour(
    streaming: ModuleType,
) -> None:
    """A reset 30 minutes ahead renders a minutes-only delta."""
    now = _at(_RESETS_AT_EPOCH - 30 * 60)
    rendered = streaming.format_resets_at(_RESETS_AT_EPOCH, now)
    assert "30m" in rendered


def test_format_resets_at_includes_delta_hours_and_minutes(
    streaming: ModuleType,
) -> None:
    """A reset 3h27m ahead renders both hours and minutes."""
    now = _at(_RESETS_AT_EPOCH - (3 * 3600 + 27 * 60))
    rendered = streaming.format_resets_at(_RESETS_AT_EPOCH, now)
    assert "3h27m" in rendered


def test_format_resets_at_handles_already_passed_reset(
    streaming: ModuleType,
) -> None:
    """A reset in the past renders without crashing."""
    now = _at(_RESETS_AT_EPOCH + 60)
    rendered = streaming.format_resets_at(_RESETS_AT_EPOCH, now)
    assert "0m" in rendered
