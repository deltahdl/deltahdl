"""Unit tests for satisfy_subclause.streaming."""

import io
from unittest.mock import MagicMock, patch

import pytest


# --- format_tool_call -------------------------------------------------------


def test_format_tool_call_file_path(streaming) -> None:
    """file_path is the preferred arg key."""
    block = {"name": "Read", "input": {"file_path": "/tmp/foo.txt"}}
    assert streaming.format_tool_call(block) == "  · Read(/tmp/foo.txt)"


def test_format_tool_call_command(streaming) -> None:
    """command is used when file_path is absent."""
    block = {"name": "Bash", "input": {"command": "ls"}}
    assert streaming.format_tool_call(block) == "  · Bash(ls)"


def test_format_tool_call_pattern(streaming) -> None:
    """pattern is used for grep-style tools."""
    block = {"name": "Grep", "input": {"pattern": "TODO"}}
    assert streaming.format_tool_call(block) == "  · Grep(TODO)"


def test_format_tool_call_path(streaming) -> None:
    """path is used when file_path is absent."""
    block = {"name": "Glob", "input": {"path": "src/"}}
    assert streaming.format_tool_call(block) == "  · Glob(src/)"


def test_format_tool_call_url(streaming) -> None:
    """url is used for fetch-style tools."""
    block = {"name": "WebFetch", "input": {"url": "https://example.com"}}
    assert streaming.format_tool_call(block) == "  · WebFetch(https://example.com)"


def test_format_tool_call_query(streaming) -> None:
    """query is used for search-style tools."""
    block = {"name": "WebSearch", "input": {"query": "claude"}}
    assert streaming.format_tool_call(block) == "  · WebSearch(claude)"


def test_format_tool_call_no_known_key(streaming) -> None:
    """Tools whose input has no recognized key fall back to no-arg form."""
    block = {"name": "Custom", "input": {"foo": "bar"}}
    assert streaming.format_tool_call(block) == "  · Custom()"


def test_format_tool_call_truncates_long_arg(streaming) -> None:
    """Arg values longer than 80 chars are truncated with an ellipsis."""
    block = {"name": "Read", "input": {"file_path": "x" * 200}}
    result = streaming.format_tool_call(block)
    assert result.endswith("...)")


def test_format_tool_call_truncated_length(streaming) -> None:
    """Truncated arg values stay within the cap including the ellipsis."""
    block = {"name": "Read", "input": {"file_path": "x" * 200}}
    result = streaming.format_tool_call(block)
    assert len(result) == len("  · Read(") + 80 + 1


def test_format_tool_call_missing_name(streaming) -> None:
    """A tool_use without a name renders as ?."""
    block = {"input": {"file_path": "/tmp/x"}}
    assert streaming.format_tool_call(block) == "  · ?(/tmp/x)"


def test_format_tool_call_missing_input(streaming) -> None:
    """A tool_use without input falls back to the no-arg form."""
    assert streaming.format_tool_call({"name": "Bash"}) == "  · Bash()"


def test_format_tool_call_null_input(streaming) -> None:
    """A tool_use with null input falls back to the no-arg form."""
    assert streaming.format_tool_call(
        {"name": "Bash", "input": None},
    ) == "  · Bash()"


# --- print_event ------------------------------------------------------------


def test_print_event_assistant_text(streaming, capsys) -> None:
    """assistant text blocks are printed verbatim."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "Hello"}]},
    })
    assert "Hello" in capsys.readouterr().out


def test_print_event_assistant_tool_use(streaming, capsys) -> None:
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
    streaming, capsys,
) -> None:
    """assistant text blocks that are whitespace-only are skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "   \n"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_thinking_block(
    streaming, capsys,
) -> None:
    """Thinking blocks render as a visible one-line marker."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "thinking", "text": "..."}]},
    })
    assert "thinking" in capsys.readouterr().out


def test_print_event_assistant_unknown_block_type(
    streaming, capsys,
) -> None:
    """Unknown assistant block types render as a [type] marker."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "weird"}]},
    })
    assert "[weird]" in capsys.readouterr().out


def test_print_event_assistant_null_content(streaming, capsys) -> None:
    """An assistant message with null content prints nothing."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": None},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_null_message(streaming, capsys) -> None:
    """An assistant event with null message prints nothing."""
    streaming.print_event({"type": "assistant", "message": None})
    assert capsys.readouterr().out == ""


def test_print_event_system_init_prints_marker(streaming, capsys) -> None:
    """System events print a one-line marker including the subtype."""
    streaming.print_event({"type": "system", "subtype": "init"})
    assert "system" in capsys.readouterr().out


def test_print_event_system_init_includes_subtype(streaming, capsys) -> None:
    """The system marker mentions the event subtype."""
    streaming.print_event({"type": "system", "subtype": "init"})
    assert "init" in capsys.readouterr().out


def test_print_event_user_tool_result_string(streaming, capsys) -> None:
    """User tool_result blocks with a string body render as a one-liner."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": "ok"},
        ]},
    })
    assert "ok" in capsys.readouterr().out


def test_print_event_user_tool_result_text_blocks(
    streaming, capsys,
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


def test_print_event_user_tool_result_truncates(streaming, capsys) -> None:
    """Long tool_result text is truncated with an ellipsis."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": "x" * 500},
        ]},
    })
    assert "..." in capsys.readouterr().out


def test_print_event_user_tool_result_empty(streaming, capsys) -> None:
    """An empty tool_result body still renders a marker."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": ""},
        ]},
    })
    assert "(empty)" in capsys.readouterr().out


def test_print_event_user_tool_result_unknown_content_type(
    streaming, capsys,
) -> None:
    """A tool_result with non-string, non-list content renders empty."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [
            {"type": "tool_result", "content": None},
        ]},
    })
    assert "(empty)" in capsys.readouterr().out


def test_print_event_user_null_content(streaming, capsys) -> None:
    """A user event with null content prints nothing."""
    streaming.print_event({"type": "user", "message": {"content": None}})
    assert capsys.readouterr().out == ""


def test_print_event_user_null_message(streaming, capsys) -> None:
    """A user event with null message prints nothing."""
    streaming.print_event({"type": "user", "message": None})
    assert capsys.readouterr().out == ""


def test_print_event_user_skips_non_tool_result_block(
    streaming, capsys,
) -> None:
    """User blocks that are not tool_result are ignored."""
    streaming.print_event({
        "type": "user",
        "message": {"content": [{"type": "text", "text": "noop"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_result_prints_marker(streaming, capsys) -> None:
    """Result events print a terminal marker."""
    streaming.print_event({"type": "result", "result": "DONE"})
    assert "result" in capsys.readouterr().out


def test_print_event_unknown_type_prints_raw(streaming, capsys) -> None:
    """Unknown event types fall back to printing the raw type."""
    streaming.print_event({"type": "weird"})
    assert "weird" in capsys.readouterr().out


def test_print_event_assistant_text_missing_text(streaming, capsys) -> None:
    """A text block with no text key is treated as empty and skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text"}]},
    })
    assert capsys.readouterr().out == ""


# --- extract_result ---------------------------------------------------------


def test_extract_result_returns_text(streaming) -> None:
    """A result event returns its .result string."""
    assert streaming.extract_result(
        {"type": "result", "result": "done"},
    ) == "done"


def test_extract_result_non_result_event(streaming) -> None:
    """Non-result events return None."""
    assert streaming.extract_result({"type": "assistant"}) is None


def test_extract_result_empty_string(streaming) -> None:
    """An empty .result returns None."""
    assert streaming.extract_result(
        {"type": "result", "result": ""},
    ) is None


def test_extract_result_non_string(streaming) -> None:
    """A non-string .result returns None."""
    assert streaming.extract_result(
        {"type": "result", "result": 42},
    ) is None


def test_extract_result_missing(streaming) -> None:
    """A result event with no .result field returns None."""
    assert streaming.extract_result({"type": "result"}) is None


# --- build_streaming_cmd ----------------------------------------------------


def test_build_streaming_cmd_starts_with_claude(streaming) -> None:
    """The argv begins with 'claude' followed by '-p'."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert cmd[:2] == ["claude", "-p"]


def test_build_streaming_cmd_carries_model(streaming) -> None:
    """The model argument is forwarded to --model."""
    cmd = streaming.build_streaming_cmd(model="haiku", disallowed_tools="X")
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_build_streaming_cmd_uses_stream_json(streaming) -> None:
    """--output-format stream-json is set so events stream live."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_build_streaming_cmd_uses_verbose(streaming) -> None:
    """--verbose is required for stream-json output."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert "--verbose" in cmd


def test_build_streaming_cmd_uses_dangerously_skip_permissions(
    streaming,
) -> None:
    """--dangerously-skip-permissions is set."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert "--dangerously-skip-permissions" in cmd


def test_build_streaming_cmd_carries_disallowed_tools(streaming) -> None:
    """The disallowed-tools string is forwarded to --disallowedTools."""
    cmd = streaming.build_streaming_cmd(
        model="opus", disallowed_tools="Bash(git *)",
    )
    assert cmd[cmd.index("--disallowedTools") + 1] == "Bash(git *)"


# --- run_claude_streaming ---------------------------------------------------


def _make_proc(stdout_lines, *, stderr="", returncode=0):
    """Build a Popen-like context manager mock."""
    proc = MagicMock()
    proc.stdout = io.StringIO("".join(stdout_lines))
    proc.stderr = MagicMock()
    proc.stderr.read.return_value = stderr
    proc.stdin = MagicMock()
    proc.wait.return_value = returncode
    cm = MagicMock()
    cm.__enter__.return_value = proc
    cm.__exit__.return_value = None
    return cm, proc


def _run(streaming, lines, *, stderr="", returncode=0):
    """Invoke run_claude_streaming with a stubbed Popen."""
    cm, proc = _make_proc(lines, stderr=stderr, returncode=returncode)
    with patch(
        "satisfy_subclause.streaming.subprocess.Popen",
        return_value=cm,
    ) as popen:
        result = streaming.run_claude_streaming(
            ["claude"], "prompt", env={"PATH": "/usr/bin"},
        )
    return result, popen, proc


_OK_STREAM = [
    '{"type":"assistant","message":{"content":'
    '[{"type":"text","text":"hi"}]}}\n',
    '{"type":"result","result":"final"}\n',
]


def test_run_claude_streaming_returns_result(streaming) -> None:
    """The terminal result event's .result is returned."""
    assert _run(streaming, _OK_STREAM)[0] == "final"


def test_run_claude_streaming_prints_startup_marker(
    streaming, capsys,
) -> None:
    """A '[claude starting]' marker prints to stderr immediately on launch."""
    _run(streaming, _OK_STREAM)
    assert "claude starting" in capsys.readouterr().err


def test_run_claude_streaming_writes_prompt(streaming) -> None:
    """The prompt is written to the child's stdin."""
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.write.call_args == (("prompt",),)


def test_run_claude_streaming_closes_stdin(streaming) -> None:
    """stdin is closed after the prompt is written."""
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.close.call_count == 1


def test_run_claude_streaming_passes_env(streaming) -> None:
    """The env mapping is forwarded to Popen."""
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[1]["env"] == {"PATH": "/usr/bin"}


def test_run_claude_streaming_passes_cmd(streaming) -> None:
    """The command list is forwarded to Popen."""
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[0][0] == ["claude"]


def test_run_claude_streaming_prints_assistant_text(
    streaming, capsys,
) -> None:
    """Assistant text is streamed to stdout while events arrive."""
    _run(streaming, _OK_STREAM)
    assert "hi" in capsys.readouterr().out


def test_run_claude_streaming_skips_blank_lines(streaming) -> None:
    """Blank lines in the stream are skipped without error."""
    lines = ["\n", "   \n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_skips_non_json_lines(streaming) -> None:
    """Lines that fail JSON decoding are skipped without error."""
    lines = ["not json\n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_exits_on_nonzero(streaming) -> None:
    """A non-zero exit code is loud-fatal."""
    with pytest.raises(SystemExit):
        _run(streaming, _OK_STREAM, returncode=1, stderr="boom")


def test_run_claude_streaming_dumps_stderr_on_nonzero(
    streaming, capsys,
) -> None:
    """Non-zero exit dumps stderr to the terminal."""
    try:
        _run(streaming, _OK_STREAM, returncode=1, stderr="UNIQUE_STDERR")
    except SystemExit:
        pass
    assert "UNIQUE_STDERR" in capsys.readouterr().err


def test_run_claude_streaming_exits_when_no_result(streaming) -> None:
    """A stream without a terminal result event is loud-fatal."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    with pytest.raises(SystemExit):
        _run(streaming, lines)


def test_run_claude_streaming_dumps_stderr_when_no_result(
    streaming, capsys,
) -> None:
    """Missing-result exit dumps stderr to the terminal."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    try:
        _run(streaming, lines, stderr="UNIQUE_NORESULT_STDERR")
    except SystemExit:
        pass
    assert "UNIQUE_NORESULT_STDERR" in capsys.readouterr().err
