"""Unit tests for the diagnostic helpers in satisfy_subclause.streaming."""

from types import ModuleType


# --- extract_session_id -----------------------------------------------------


def test_extract_session_id_returns_string(streaming: ModuleType) -> None:
    """A system event with a string session_id returns it."""
    assert streaming.extract_session_id(
        {"type": "system", "session_id": "sid-123"},
    ) == "sid-123"


def test_extract_session_id_non_system_event(streaming: ModuleType) -> None:
    """Non-system events return None."""
    assert streaming.extract_session_id(
        {"type": "assistant"},
    ) is None


def test_extract_session_id_non_string_value(streaming: ModuleType) -> None:
    """A non-string session_id field is treated as missing."""
    assert streaming.extract_session_id(
        {"type": "system", "session_id": 42},
    ) is None


def test_extract_session_id_missing_field(streaming: ModuleType) -> None:
    """A system event without a session_id field returns None."""
    assert streaming.extract_session_id({"type": "system"}) is None


# --- extract_tool_name ------------------------------------------------------


def test_extract_tool_name_finds_tool_use(streaming: ModuleType) -> None:
    """An assistant event whose last block is tool_use returns its name."""
    event = {
        "type": "assistant",
        "message": {"content": [
            {"type": "text", "text": "hi"},
            {"type": "tool_use", "name": "TodoWrite"},
        ]},
    }
    assert streaming.extract_tool_name(event) == "TodoWrite"


def test_extract_tool_name_non_assistant_event(streaming: ModuleType) -> None:
    """Non-assistant events return None."""
    assert streaming.extract_tool_name({"type": "user"}) is None


def test_extract_tool_name_no_tool_use_block(streaming: ModuleType) -> None:
    """Assistant events with no tool_use block return None."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "hi"}]},
    }
    assert streaming.extract_tool_name(event) is None


def test_extract_tool_name_null_message(streaming: ModuleType) -> None:
    """An assistant event with null message returns None."""
    assert streaming.extract_tool_name(
        {"type": "assistant", "message": None},
    ) is None


# --- describe_assistant_blocks ----------------------------------------------


def test_describe_assistant_blocks_tool_use(streaming: ModuleType) -> None:
    """A trailing tool_use block names the tool."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "tool_use", "name": "Read"}]},
    }
    assert streaming.describe_assistant_blocks(event) == "tool_use:Read"


def test_describe_assistant_blocks_tool_use_missing_name(streaming: ModuleType) -> None:
    """A tool_use block without a name renders as ?."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "tool_use"}]},
    }
    assert streaming.describe_assistant_blocks(event) == "tool_use:?"


def test_describe_assistant_blocks_thinking(streaming: ModuleType) -> None:
    """A trailing thinking block renders as 'thinking'."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "thinking", "text": "..."}]},
    }
    assert streaming.describe_assistant_blocks(event) == "thinking"


def test_describe_assistant_blocks_text(streaming: ModuleType) -> None:
    """A trailing text block renders as 'text'."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "hi"}]},
    }
    assert streaming.describe_assistant_blocks(event) == "text"


def test_describe_assistant_blocks_empty(streaming: ModuleType) -> None:
    """An empty content list renders as '(empty)'."""
    event = {"type": "assistant", "message": {"content": []}}
    assert streaming.describe_assistant_blocks(event) == "(empty)"


def test_describe_assistant_blocks_null_content(streaming: ModuleType) -> None:
    """Null content renders as '(empty)'."""
    event = {"type": "assistant", "message": {"content": None}}
    assert streaming.describe_assistant_blocks(event) == "(empty)"


def test_describe_assistant_blocks_unknown_block_type(streaming: ModuleType) -> None:
    """Content of only unknown block types renders as '(empty)'."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "weird"}]},
    }
    assert streaming.describe_assistant_blocks(event) == "(empty)"


# --- describe_user_blocks ---------------------------------------------------


def test_describe_user_blocks_tool_result_with_tool_name(streaming: ModuleType) -> None:
    """A tool_result with a known tool name names the tool."""
    event = {
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": "ok"},
        ]},
    }
    assert streaming.describe_user_blocks(
        event, "TodoWrite",
    ) == "tool_result for TodoWrite"


def test_describe_user_blocks_tool_result_without_tool_name(
    streaming: ModuleType,
) -> None:
    """A tool_result without a known tool name renders bare."""
    event = {
        "type": "user",
        "message": {"content": [{"type": "tool_result", "content": "ok"}]},
    }
    assert streaming.describe_user_blocks(event, None) == "tool_result"


def test_describe_user_blocks_no_tool_result(streaming: ModuleType) -> None:
    """A user event without tool_result renders as 'user (other)'."""
    event = {
        "type": "user",
        "message": {"content": [{"type": "text", "text": "hi"}]},
    }
    assert streaming.describe_user_blocks(event, None) == "user (other)"


# --- describe_result_event --------------------------------------------------


def test_describe_result_event_success(streaming: ModuleType) -> None:
    """A success result event renders the subtype after 'result:'."""
    assert streaming.describe_result_event(
        {"type": "result", "subtype": "success"},
    ) == "result:success"


def test_describe_result_event_success_default_subtype(streaming: ModuleType) -> None:
    """A success result with no subtype defaults to 'success'."""
    assert streaming.describe_result_event(
        {"type": "result"},
    ) == "result:success"


def test_describe_result_event_is_error(streaming: ModuleType) -> None:
    """An is_error result event prefixes the subtype with 'result(is_error):'."""
    assert streaming.describe_result_event(
        {"type": "result", "is_error": True, "subtype": "error_api"},
    ) == "result(is_error):error_api"


def test_describe_result_event_is_error_default_subtype(streaming: ModuleType) -> None:
    """An is_error result with no subtype renders '?'."""
    assert streaming.describe_result_event(
        {"type": "result", "is_error": True},
    ) == "result(is_error):?"


# --- describe_event ---------------------------------------------------------


def test_describe_event_assistant(streaming: ModuleType) -> None:
    """An assistant event delegates to describe_assistant_blocks."""
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "text"}]},
    }
    assert streaming.describe_event(event, None) == "assistant text"


def test_describe_event_user(streaming: ModuleType) -> None:
    """A user event delegates to describe_user_blocks."""
    event = {
        "type": "user",
        "message": {"content": [{"type": "tool_result", "content": "ok"}]},
    }
    assert streaming.describe_event(event, "X") == "tool_result for X"


def test_describe_event_system(streaming: ModuleType) -> None:
    """A system event renders 'system:SUBTYPE'."""
    assert streaming.describe_event(
        {"type": "system", "subtype": "init"}, None,
    ) == "system:init"


def test_describe_event_system_no_subtype(streaming: ModuleType) -> None:
    """A system event without a subtype renders '?' as the subtype."""
    assert streaming.describe_event(
        {"type": "system"}, None,
    ) == "system:?"


def test_describe_event_result(streaming: ModuleType) -> None:
    """A result event delegates to describe_result_event."""
    assert streaming.describe_event(
        {"type": "result", "subtype": "success"}, None,
    ) == "result:success"


def test_describe_event_unknown_type(streaming: ModuleType) -> None:
    """Unknown event types render their type string."""
    assert streaming.describe_event({"type": "weird"}, None) == "weird"


def test_describe_event_missing_type(streaming: ModuleType) -> None:
    """An event without a type renders 'unknown'."""
    assert streaming.describe_event({}, None) == "unknown"
