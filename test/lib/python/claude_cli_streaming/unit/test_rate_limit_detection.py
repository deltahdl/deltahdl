"""Unit tests for rate-limit detection helpers in lib.python.claude_cli_streaming."""

from types import ModuleType


# --- is_rate_limit_event_error ----------------------------------------------


def test_is_rate_limit_event_error_matches_synthetic_429(
    streaming: ModuleType,
) -> None:
    """An assistant event with apiErrorStatus=429 and error=rate_limit matches."""
    event = {
        "type": "assistant",
        "apiErrorStatus": 429,
        "error": "rate_limit",
        "message": {"content": [{"type": "text", "text": "..."}]},
    }
    assert streaming.is_rate_limit_event_error(event) is True


def test_is_rate_limit_event_error_rejects_non_assistant(
    streaming: ModuleType,
) -> None:
    """Result events with the same fields do not match this helper."""
    event = {"type": "result", "apiErrorStatus": 429, "error": "rate_limit"}
    assert streaming.is_rate_limit_event_error(event) is False


def test_is_rate_limit_event_error_rejects_non_429(streaming: ModuleType) -> None:
    """An assistant event with a non-429 status does not match."""
    event = {
        "type": "assistant", "apiErrorStatus": 500, "error": "rate_limit",
    }
    assert streaming.is_rate_limit_event_error(event) is False


def test_is_rate_limit_event_error_rejects_other_error(
    streaming: ModuleType,
) -> None:
    """A 429 with a non-rate-limit error string does not match."""
    event = {
        "type": "assistant", "apiErrorStatus": 429, "error": "overloaded",
    }
    assert streaming.is_rate_limit_event_error(event) is False


def test_is_rate_limit_event_error_rejects_missing_fields(
    streaming: ModuleType,
) -> None:
    """An assistant event without the 429 fields does not match."""
    assert streaming.is_rate_limit_event_error({"type": "assistant"}) is False


# --- extract_rate_limit_info ------------------------------------------------


def test_extract_rate_limit_info_returns_payload(streaming: ModuleType) -> None:
    """A rate_limit_event returns its rate_limit_info dict."""
    info = {"status": "exceeded", "resetsAt": 1779592200}
    event = {"type": "rate_limit_event", "rate_limit_info": info}
    assert streaming.extract_rate_limit_info(event) == info


def test_extract_rate_limit_info_returns_none_on_other_event(
    streaming: ModuleType,
) -> None:
    """Non-rate-limit events return None."""
    assert streaming.extract_rate_limit_info({"type": "assistant"}) is None


def test_extract_rate_limit_info_returns_none_when_missing_payload(
    streaming: ModuleType,
) -> None:
    """A rate_limit_event without rate_limit_info returns None."""
    assert streaming.extract_rate_limit_info(
        {"type": "rate_limit_event"},
    ) is None


def test_extract_rate_limit_info_returns_none_when_payload_non_dict(
    streaming: ModuleType,
) -> None:
    """A rate_limit_info field that is not a dict is treated as missing."""
    event = {"type": "rate_limit_event", "rate_limit_info": "scalar"}
    assert streaming.extract_rate_limit_info(event) is None


# --- extract_synthetic_text -------------------------------------------------


def test_extract_synthetic_text_returns_first_text_block(
    streaming: ModuleType,
) -> None:
    """An assistant event's first text block content is returned."""
    event = {
        "type": "assistant",
        "message": {"content": [
            {"type": "text", "text": "Usage credits are required."},
        ]},
    }
    assert streaming.extract_synthetic_text(event) == (
        "Usage credits are required."
    )


def test_extract_synthetic_text_skips_non_text_blocks(streaming: ModuleType) -> None:
    """The first text block is returned even when preceded by other types."""
    event = {
        "type": "assistant",
        "message": {"content": [
            {"type": "thinking", "text": "..."},
            {"type": "text", "text": "hello"},
        ]},
    }
    assert streaming.extract_synthetic_text(event) == "hello"


def test_extract_synthetic_text_returns_none_when_no_text_block(
    streaming: ModuleType,
) -> None:
    """An assistant event with no text blocks returns None."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "tool_use", "name": "Read"}]},
    }
    assert streaming.extract_synthetic_text(event) is None


def test_extract_synthetic_text_returns_none_when_message_missing(
    streaming: ModuleType,
) -> None:
    """An event without a message returns None."""
    assert streaming.extract_synthetic_text({"type": "assistant"}) is None


def test_extract_synthetic_text_returns_none_when_message_null(
    streaming: ModuleType,
) -> None:
    """An event with message=None returns None."""
    assert streaming.extract_synthetic_text(
        {"type": "assistant", "message": None},
    ) is None


def test_extract_synthetic_text_returns_none_when_content_missing(
    streaming: ModuleType,
) -> None:
    """A message without content returns None."""
    assert streaming.extract_synthetic_text(
        {"type": "assistant", "message": {}},
    ) is None


def test_extract_synthetic_text_skips_text_block_with_non_string_text(
    streaming: ModuleType,
) -> None:
    """A text block whose .text field is non-string is skipped; a later valid block wins."""
    event = {
        "type": "assistant",
        "message": {"content": [
            {"type": "text", "text": 42},
            {"type": "text", "text": "fallback"},
        ]},
    }
    assert streaming.extract_synthetic_text(event) == "fallback"


# --- is_rate_limit_result_event ---------------------------------------------


def test_is_rate_limit_result_event_matches_429_error_result(
    streaming: ModuleType,
) -> None:
    """A result event with is_error and api_error_status=429 matches."""
    event = {
        "type": "result", "is_error": True, "api_error_status": 429,
    }
    assert streaming.is_rate_limit_result_event(event) is True


def test_is_rate_limit_result_event_rejects_success_result(
    streaming: ModuleType,
) -> None:
    """A successful result event does not match."""
    event = {"type": "result", "is_error": False, "api_error_status": None}
    assert streaming.is_rate_limit_result_event(event) is False


def test_is_rate_limit_result_event_rejects_non_429_error(
    streaming: ModuleType,
) -> None:
    """An error result with a non-429 status does not match."""
    event = {
        "type": "result", "is_error": True, "api_error_status": 500,
    }
    assert streaming.is_rate_limit_result_event(event) is False


def test_is_rate_limit_result_event_rejects_non_result(
    streaming: ModuleType,
) -> None:
    """Non-result events do not match even with the same fields."""
    event = {
        "type": "assistant", "is_error": True, "api_error_status": 429,
    }
    assert streaming.is_rate_limit_result_event(event) is False
