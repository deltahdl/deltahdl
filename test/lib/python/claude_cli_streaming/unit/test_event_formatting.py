"""Unit tests for assistant/user event formatting in claude_cli_streaming."""

from types import ModuleType

import pytest


# --- format_tool_call -------------------------------------------------------


def test_format_tool_call_file_path(streaming: ModuleType) -> None:
    """file_path is the preferred arg key."""
    block = {"name": "Read", "input": {"file_path": "/tmp/foo.txt"}}
    assert streaming.format_tool_call(block) == "  · Read(/tmp/foo.txt)"


def test_format_tool_call_command(streaming: ModuleType) -> None:
    """command is used when file_path is absent."""
    block = {"name": "Bash", "input": {"command": "ls"}}
    assert streaming.format_tool_call(block) == "  · Bash(ls)"


def test_format_tool_call_pattern(streaming: ModuleType) -> None:
    """pattern is used for grep-style tools."""
    block = {"name": "Grep", "input": {"pattern": "TODO"}}
    assert streaming.format_tool_call(block) == "  · Grep(TODO)"


def test_format_tool_call_path(streaming: ModuleType) -> None:
    """path is used when file_path is absent."""
    block = {"name": "Glob", "input": {"path": "src/"}}
    assert streaming.format_tool_call(block) == "  · Glob(src/)"


def test_format_tool_call_url(streaming: ModuleType) -> None:
    """url is used for fetch-style tools."""
    block = {"name": "WebFetch", "input": {"url": "https://example.com"}}
    assert streaming.format_tool_call(block) == "  · WebFetch(https://example.com)"


def test_format_tool_call_query(streaming: ModuleType) -> None:
    """query is used for search-style tools."""
    block = {"name": "WebSearch", "input": {"query": "claude"}}
    assert streaming.format_tool_call(block) == "  · WebSearch(claude)"


def test_format_tool_call_no_known_key(streaming: ModuleType) -> None:
    """Tools whose input has no recognized key fall back to no-arg form."""
    block = {"name": "Custom", "input": {"foo": "bar"}}
    assert streaming.format_tool_call(block) == "  · Custom()"


def test_format_tool_call_truncates_long_arg(streaming: ModuleType) -> None:
    """Arg values longer than 80 chars are truncated with an ellipsis."""
    block = {"name": "Read", "input": {"file_path": "x" * 200}}
    result = streaming.format_tool_call(block)
    assert result.endswith("...)")


def test_format_tool_call_truncated_length(streaming: ModuleType) -> None:
    """Truncated arg values stay within the cap including the ellipsis."""
    block = {"name": "Read", "input": {"file_path": "x" * 200}}
    result = streaming.format_tool_call(block)
    assert len(result) == len("  · Read(") + 80 + 1


def test_format_tool_call_missing_name(streaming: ModuleType) -> None:
    """A tool_use without a name renders as ?."""
    block = {"input": {"file_path": "/tmp/x"}}
    assert streaming.format_tool_call(block) == "  · ?(/tmp/x)"


def test_format_tool_call_missing_input(streaming: ModuleType) -> None:
    """A tool_use without input falls back to the no-arg form."""
    assert streaming.format_tool_call({"name": "Bash"}) == "  · Bash()"


def test_format_tool_call_null_input(streaming: ModuleType) -> None:
    """A tool_use with null input falls back to the no-arg form."""
    assert streaming.format_tool_call(
        {"name": "Bash", "input": None},
    ) == "  · Bash()"


# --- print_event ------------------------------------------------------------


def test_print_event_assistant_text(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """assistant text blocks are printed verbatim."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "Hello"}]},
    })
    assert "Hello" in capsys.readouterr().out


def test_print_event_assistant_tool_use(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """assistant tool_use blocks are printed as one-line summaries."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [
            {"type": "tool_use", "name": "Read",
             "input": {"file_path": "/x"}},
        ]},
    })
    assert "· Read(/x)" in capsys.readouterr().out


def test_print_event_assistant_skips_whitespace_text(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """assistant text blocks that are whitespace-only are skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "   \n"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_thinking_block(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Thinking blocks render as a visible one-line marker."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "thinking", "text": "..."}]},
    })
    assert "thinking" in capsys.readouterr().out


def test_print_event_assistant_unknown_block_type(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Unknown assistant block types are silently consumed."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "weird"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_null_content(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """An assistant message with null content prints nothing."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": None},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_null_message(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """An assistant event with null message prints nothing."""
    streaming.print_event({"type": "assistant", "message": None})
    assert capsys.readouterr().out == ""


def test_print_event_system_is_silent(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """System events are consumed silently."""
    streaming.print_event({"type": "system", "subtype": "init"})
    assert capsys.readouterr().out == ""


def test_print_event_user_tool_result_string(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """User tool_result blocks with a string body render as a one-liner."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": "ok"},
        ]},
    })
    assert "ok" in capsys.readouterr().out


def test_print_event_user_tool_result_text_blocks(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """User tool_result blocks with nested text blocks render their text."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": [
                {"type": "text", "text": "fileA\nfileB"},
            ]},
        ]},
    })
    assert "fileA" in capsys.readouterr().out


def test_print_event_user_tool_result_truncates(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Long tool_result text is truncated with an ellipsis."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": "x" * 500},
        ]},
    })
    assert "..." in capsys.readouterr().out


def test_print_event_user_tool_result_empty(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """An empty tool_result body still renders a marker."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": ""},
        ]},
    })
    assert "(empty)" in capsys.readouterr().out


def test_print_event_user_tool_result_unknown_content_type(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """A tool_result with non-string, non-list content renders empty."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": None},
        ]},
    })
    assert "(empty)" in capsys.readouterr().out


def test_print_event_user_null_content(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """A user event with null content prints nothing."""
    streaming.print_event({"type": "user", "message": {"content": None}})
    assert capsys.readouterr().out == ""


def test_print_event_user_null_message(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """A user event with null message prints nothing."""
    streaming.print_event({"type": "user", "message": None})
    assert capsys.readouterr().out == ""


def test_print_event_user_skips_non_tool_result_block(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """User blocks that are not tool_result are ignored."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [{"type": "text", "text": "noop"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_result_is_silent(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Result events are consumed silently."""
    streaming.print_event({"type": "result", "result": "DONE"})
    assert capsys.readouterr().out == ""


def test_print_event_unknown_type_is_silent(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Unknown event types are consumed silently."""
    streaming.print_event({"type": "weird"})
    assert capsys.readouterr().out == ""


def test_print_event_assistant_text_missing_text(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """A text block with no text key is treated as empty and skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text"}]},
    })
    assert capsys.readouterr().out == ""
