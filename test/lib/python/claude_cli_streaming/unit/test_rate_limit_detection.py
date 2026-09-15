from types import ModuleType


def test_is_rate_limit_event_error_matches_synthetic_429(
    streaming: ModuleType,
) -> None:
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
    event = {"type": "result", "apiErrorStatus": 429, "error": "rate_limit"}
    assert streaming.is_rate_limit_event_error(event) is False


def test_is_rate_limit_event_error_rejects_non_429(streaming: ModuleType) -> None:
    event = {
        "type": "assistant", "apiErrorStatus": 500, "error": "rate_limit",
    }
    assert streaming.is_rate_limit_event_error(event) is False


def test_is_rate_limit_event_error_rejects_other_error(
    streaming: ModuleType,
) -> None:
    event = {
        "type": "assistant", "apiErrorStatus": 429, "error": "overloaded",
    }
    assert streaming.is_rate_limit_event_error(event) is False


def test_is_rate_limit_event_error_rejects_missing_fields(
    streaming: ModuleType,
) -> None:
    assert streaming.is_rate_limit_event_error({"type": "assistant"}) is False


def test_extract_rate_limit_info_returns_payload(streaming: ModuleType) -> None:
    info = {"status": "exceeded", "resetsAt": 1779592200}
    event = {"type": "rate_limit_event", "rate_limit_info": info}
    assert streaming.extract_rate_limit_info(event) == info


def test_extract_rate_limit_info_returns_none_on_other_event(
    streaming: ModuleType,
) -> None:
    assert streaming.extract_rate_limit_info({"type": "assistant"}) is None


def test_extract_rate_limit_info_returns_none_when_missing_payload(
    streaming: ModuleType,
) -> None:
    assert streaming.extract_rate_limit_info(
        {"type": "rate_limit_event"},
    ) is None


def test_extract_rate_limit_info_returns_none_when_payload_non_dict(
    streaming: ModuleType,
) -> None:
    event = {"type": "rate_limit_event", "rate_limit_info": "scalar"}
    assert streaming.extract_rate_limit_info(event) is None


def test_extract_synthetic_text_returns_first_text_block(
    streaming: ModuleType,
) -> None:
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
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "tool_use", "name": "Read"}]},
    }
    assert streaming.extract_synthetic_text(event) is None


def test_extract_synthetic_text_returns_none_when_message_missing(
    streaming: ModuleType,
) -> None:
    assert streaming.extract_synthetic_text({"type": "assistant"}) is None


def test_extract_synthetic_text_returns_none_when_message_null(
    streaming: ModuleType,
) -> None:
    assert streaming.extract_synthetic_text(
        {"type": "assistant", "message": None},
    ) is None


def test_extract_synthetic_text_returns_none_when_content_missing(
    streaming: ModuleType,
) -> None:
    assert streaming.extract_synthetic_text(
        {"type": "assistant", "message": {}},
    ) is None


def test_extract_synthetic_text_skips_text_block_with_non_string_text(
    streaming: ModuleType,
) -> None:
    event = {
        "type": "assistant",
        "message": {"content": [
            {"type": "text", "text": 42},
            {"type": "text", "text": "fallback"},
        ]},
    }
    assert streaming.extract_synthetic_text(event) == "fallback"


def test_is_rate_limit_result_event_matches_429_error_result(
    streaming: ModuleType,
) -> None:
    event = {
        "type": "result", "is_error": True, "api_error_status": 429,
    }
    assert streaming.is_rate_limit_result_event(event) is True


def test_is_rate_limit_result_event_rejects_success_result(
    streaming: ModuleType,
) -> None:
    event = {"type": "result", "is_error": False, "api_error_status": None}
    assert streaming.is_rate_limit_result_event(event) is False


def test_is_rate_limit_result_event_rejects_non_429_error(
    streaming: ModuleType,
) -> None:
    event = {
        "type": "result", "is_error": True, "api_error_status": 500,
    }
    assert streaming.is_rate_limit_result_event(event) is False


def test_is_rate_limit_result_event_rejects_non_result(
    streaming: ModuleType,
) -> None:
    event = {
        "type": "assistant", "is_error": True, "api_error_status": 429,
    }
    assert streaming.is_rate_limit_result_event(event) is False
