"""Unit tests for the RateLimitError public exception type."""

from types import ModuleType


_FULL_INFO_PAYLOAD: dict[str, object] = {
    "rateLimitType": "five_hour",
    "resetsAt": 1779592200,
    "overageStatus": "rejected",
    "overageDisabledReason": "org_level_disabled",
}


# --- RateLimitError ---------------------------------------------------------


def test_rate_limit_error_is_exception(streaming: ModuleType) -> None:
    """RateLimitError is exposed as an Exception subclass."""
    assert issubclass(streaming.RateLimitError, Exception)


def test_rate_limit_error_carries_rate_limit_type(streaming: ModuleType) -> None:
    """The exception unpacks rateLimitType from the info payload."""
    exc = streaming.RateLimitError(
        rate_limit_info=_FULL_INFO_PAYLOAD,
        synthetic_text="...", stderr="",
    )
    assert exc.rate_limit_type == "five_hour"


def test_rate_limit_error_carries_resets_at(streaming: ModuleType) -> None:
    """The exception unpacks resetsAt from the info payload."""
    exc = streaming.RateLimitError(
        rate_limit_info=_FULL_INFO_PAYLOAD,
        synthetic_text=None, stderr="",
    )
    assert exc.resets_at == 1779592200


def test_rate_limit_error_carries_overage_status(streaming: ModuleType) -> None:
    """The exception unpacks overageStatus from the info payload."""
    exc = streaming.RateLimitError(
        rate_limit_info=_FULL_INFO_PAYLOAD,
        synthetic_text=None, stderr="",
    )
    assert exc.overage_status == "rejected"


def test_rate_limit_error_carries_overage_disabled_reason(
    streaming: ModuleType,
) -> None:
    """The exception unpacks overageDisabledReason from the info payload."""
    exc = streaming.RateLimitError(
        rate_limit_info=_FULL_INFO_PAYLOAD,
        synthetic_text=None, stderr="",
    )
    assert exc.overage_disabled_reason == "org_level_disabled"


def test_rate_limit_error_carries_synthetic_text(streaming: ModuleType) -> None:
    """The exception preserves the CLI's synthetic message text."""
    exc = streaming.RateLimitError(
        rate_limit_info=None,
        synthetic_text="Usage credits are required.", stderr="",
    )
    assert exc.synthetic_text == "Usage credits are required."


def test_rate_limit_error_carries_stderr(streaming: ModuleType) -> None:
    """The exception preserves the captured stderr for the loud-fatal."""
    exc = streaming.RateLimitError(
        rate_limit_info=None,
        synthetic_text=None, stderr="UNIQUE_RATE_LIMIT_STDERR",
    )
    assert exc.stderr == "UNIQUE_RATE_LIMIT_STDERR"


def test_rate_limit_error_handles_none_info(streaming: ModuleType) -> None:
    """rate_limit_info=None flattens every attribute to None."""
    exc = streaming.RateLimitError(
        rate_limit_info=None, synthetic_text=None, stderr="",
    )
    assert (
        exc.rate_limit_type, exc.resets_at,
        exc.overage_status, exc.overage_disabled_reason,
    ) == (None, None, None, None)


def test_rate_limit_error_handles_partial_info(streaming: ModuleType) -> None:
    """Missing sub-keys default to None rather than raising KeyError."""
    exc = streaming.RateLimitError(
        rate_limit_info={"rateLimitType": "five_hour"},
        synthetic_text=None, stderr="",
    )
    assert (exc.rate_limit_type, exc.resets_at) == ("five_hour", None)


def test_rate_limit_error_str_includes_rate_limit_type(
    streaming: ModuleType,
) -> None:
    """str(exception) names the rate-limit type for log correlation."""
    exc = streaming.RateLimitError(
        rate_limit_info=_FULL_INFO_PAYLOAD,
        synthetic_text=None, stderr="",
    )
    assert "five_hour" in str(exc)


def test_rate_limit_error_str_includes_resets_at(streaming: ModuleType) -> None:
    """str(exception) includes the resetsAt epoch for log correlation."""
    exc = streaming.RateLimitError(
        rate_limit_info=_FULL_INFO_PAYLOAD,
        synthetic_text=None, stderr="",
    )
    assert "1779592200" in str(exc)
