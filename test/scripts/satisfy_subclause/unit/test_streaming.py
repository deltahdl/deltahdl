"""Unit tests for satisfy_subclause.streaming."""

import io
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

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


# --- extract_result ---------------------------------------------------------


def test_extract_result_returns_text(streaming: ModuleType) -> None:
    """A result event returns its .result string."""
    assert streaming.extract_result(
        {"type": "result", "result": "done"},
    ) == "done"


def test_extract_result_non_result_event(streaming: ModuleType) -> None:
    """Non-result events return None."""
    assert streaming.extract_result({"type": "assistant"}) is None


def test_extract_result_empty_string(streaming: ModuleType) -> None:
    """An empty .result returns None."""
    assert streaming.extract_result(
        {"type": "result", "result": ""},
    ) is None


def test_extract_result_non_string(streaming: ModuleType) -> None:
    """A non-string .result returns None."""
    assert streaming.extract_result(
        {"type": "result", "result": 42},
    ) is None


def test_extract_result_missing(streaming: ModuleType) -> None:
    """A result event with no .result field returns None."""
    assert streaming.extract_result({"type": "result"}) is None


# --- build_streaming_cmd ----------------------------------------------------


def test_build_streaming_cmd_starts_with_claude(streaming: ModuleType) -> None:
    """The argv begins with 'claude' followed by '-p'."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert cmd[:2] == ["claude", "-p"]


def test_build_streaming_cmd_carries_model(streaming: ModuleType) -> None:
    """The model argument is forwarded to --model."""
    cmd = streaming.build_streaming_cmd(model="haiku", disallowed_tools="X")
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_build_streaming_cmd_uses_stream_json(streaming: ModuleType) -> None:
    """--output-format stream-json is set so events stream live."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_build_streaming_cmd_uses_verbose(streaming: ModuleType) -> None:
    """--verbose is required for stream-json output."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert "--verbose" in cmd


def test_build_streaming_cmd_uses_dangerously_skip_permissions(
    streaming: ModuleType,
) -> None:
    """--dangerously-skip-permissions is set."""
    cmd = streaming.build_streaming_cmd(model="opus", disallowed_tools="X")
    assert "--dangerously-skip-permissions" in cmd


def test_build_streaming_cmd_carries_disallowed_tools(streaming: ModuleType) -> None:
    """The disallowed-tools string is forwarded to --disallowedTools."""
    cmd = streaming.build_streaming_cmd(
        model="opus", disallowed_tools="Bash(git *)",
    )
    assert cmd[cmd.index("--disallowedTools") + 1] == "Bash(git *)"


# --- run_claude_streaming ---------------------------------------------------


def _make_proc(
    stdout_lines: list[str], *, stderr: str = "", returncode: int = 0,
) -> tuple[MagicMock, MagicMock]:
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


def _run(
    streaming: ModuleType, lines: list[str],
    *, stderr: str = "", returncode: int = 0,
) -> tuple[Any, MagicMock, MagicMock]:
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


def test_run_claude_streaming_returns_result(streaming: ModuleType) -> None:
    """The terminal result event's .result is returned."""
    assert _run(streaming, _OK_STREAM)[0] == "final"


def test_run_claude_streaming_writes_prompt(streaming: ModuleType) -> None:
    """The prompt is written to the child's stdin."""
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.write.call_args == (("prompt",),)


def test_run_claude_streaming_closes_stdin(streaming: ModuleType) -> None:
    """stdin is closed after the prompt is written."""
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.close.call_count == 1


def test_run_claude_streaming_passes_env(streaming: ModuleType) -> None:
    """The env mapping is forwarded to Popen."""
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[1]["env"] == {"PATH": "/usr/bin"}


def test_run_claude_streaming_passes_cmd(streaming: ModuleType) -> None:
    """The command list is forwarded to Popen."""
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[0][0] == ["claude"]


def test_run_claude_streaming_prints_assistant_text(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Assistant text is streamed to stdout while events arrive."""
    _run(streaming, _OK_STREAM)
    assert "hi" in capsys.readouterr().out


def test_run_claude_streaming_skips_blank_lines(streaming: ModuleType) -> None:
    """Blank lines in the stream are skipped without error."""
    lines = ["\n", "   \n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_skips_non_json_lines(streaming: ModuleType) -> None:
    """Lines that fail JSON decoding are skipped without error."""
    lines = ["not json\n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_exits_on_nonzero(streaming: ModuleType) -> None:
    """A non-zero exit code is loud-fatal."""
    with pytest.raises(SystemExit):
        _run(streaming, _OK_STREAM, returncode=1, stderr="boom")


def test_run_claude_streaming_dumps_stderr_on_nonzero(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Non-zero exit dumps stderr to the terminal."""
    try:
        _run(streaming, _OK_STREAM, returncode=1, stderr="UNIQUE_STDERR")
    except SystemExit:
        pass
    assert "UNIQUE_STDERR" in capsys.readouterr().err


def test_run_claude_streaming_raises_missing_result_event(streaming: ModuleType) -> None:
    """A stream without a terminal result event raises MissingResultEventError."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    with pytest.raises(streaming.MissingResultEventError):
        _run(streaming, lines)


def _run_capturing_missing_result(
    streaming: ModuleType, lines: list[str], *, stderr: str = "",
) -> Any:
    """Run with a stubbed Popen and return the MissingResultEventError raised."""
    try:
        _run(streaming, lines, stderr=stderr)
    except streaming.MissingResultEventError as exc:
        return exc
    raise RuntimeError("expected MissingResultEventError, got success")


def test_run_claude_streaming_missing_result_carries_stderr(streaming: ModuleType) -> None:
    """MissingResultEventError carries stderr so the retry wrapper can surface it."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(
        streaming, lines, stderr="UNIQUE_NORESULT_STDERR",
    )
    assert exc.stderr == "UNIQUE_NORESULT_STDERR"


# --- ContentFilterError + extract_error_result ------------------------------


def test_content_filter_error_is_exception(streaming: ModuleType) -> None:
    """ContentFilterError is exposed as an Exception subclass."""
    assert issubclass(streaming.ContentFilterError, Exception)


def test_extract_error_result_returns_none_for_non_result(streaming: ModuleType) -> None:
    """Non-result events return None."""
    assert streaming.extract_error_result({"type": "assistant"}) is None


def test_extract_error_result_returns_none_for_success_result(
    streaming: ModuleType,
) -> None:
    """Success result events (no is_error) return None."""
    assert streaming.extract_error_result(
        {"type": "result", "result": "ok"},
    ) is None


def test_extract_error_result_describes_subtype(streaming: ModuleType) -> None:
    """Error result events surface the subtype."""
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
        "errors": ["upstream went sideways"],
    })
    assert "error_api" in text


def test_extract_error_result_describes_errors(streaming: ModuleType) -> None:
    """Error result events surface the errors list."""
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
        "errors": ["upstream went sideways"],
    })
    assert "upstream went sideways" in text


def test_extract_error_result_handles_missing_errors(streaming: ModuleType) -> None:
    """Error result events with no errors list still produce a description."""
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
    })
    assert "error_api" in text


def test_extract_error_result_handles_non_list_errors(streaming: ModuleType) -> None:
    """Error result events whose errors field is a string survive."""
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
        "errors": "scalar error body",
    })
    assert "scalar error body" in text


# --- run_claude_streaming: error result events ------------------------------


_ERROR_RESULT_LINE = (
    '{"type":"result","subtype":"error_api","is_error":true,'
    '"errors":["upstream blew up"]}\n'
)


def test_run_claude_streaming_exits_on_error_result(streaming: ModuleType) -> None:
    """A non-content-filter is_error result event is loud-fatal."""
    with pytest.raises(SystemExit):
        _run(streaming, [_ERROR_RESULT_LINE])


def test_run_claude_streaming_error_result_message_includes_subtype(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The exit message names the result event's subtype."""
    try:
        _run(streaming, [_ERROR_RESULT_LINE])
    except SystemExit:
        pass
    assert "error_api" in capsys.readouterr().err


def test_run_claude_streaming_error_result_message_includes_errors(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The exit message includes the result event's errors body."""
    try:
        _run(streaming, [_ERROR_RESULT_LINE])
    except SystemExit:
        pass
    assert "upstream blew up" in capsys.readouterr().err


# --- run_claude_streaming: content-filter detection -------------------------


def test_run_claude_streaming_raises_on_raw_content_filter_marker(
    streaming: ModuleType,
) -> None:
    """A raw stdout line containing the filter marker raises ContentFilterError."""
    lines = [
        "diagnostic: blocked by content filtering policy\n",
    ]
    with pytest.raises(streaming.ContentFilterError):
        _run(streaming, lines)


def test_run_claude_streaming_raises_on_content_filter_in_error_result(
    streaming: ModuleType,
) -> None:
    """An is_error result event whose errors mention the filter raises."""
    lines = [
        '{"type":"result","subtype":"error_api","is_error":true,'
        '"errors":["response was blocked by content filtering"]}\n',
    ]
    with pytest.raises(streaming.ContentFilterError):
        _run(streaming, lines)


def test_run_claude_streaming_raises_on_stderr_content_filter(
    streaming: ModuleType,
) -> None:
    """A non-zero exit with stderr mentioning the filter raises."""
    with pytest.raises(streaming.ContentFilterError):
        _run(
            streaming,
            _OK_STREAM,
            returncode=1,
            stderr="message blocked by content filtering",
        )


# --- run_claude_streaming_with_retry ----------------------------------------


def _run_retry(
    streaming: ModuleType, side_effects: list[Any],
    *, role: str = "Step", retry_cmd: list[str] | None = None,
) -> tuple[MagicMock, Any, SystemExit | None]:
    """Patch the inner call and invoke run_claude_streaming_with_retry."""
    if retry_cmd is None:
        retry_cmd = ["claude", "--continue"]
    inner_patch = patch.object(
        streaming, "run_claude_streaming", side_effect=side_effects,
    )
    with inner_patch as inner:
        result = None
        try:
            result = streaming.run_claude_streaming_with_retry(
                ["claude"], "orig", env={}, retry_cmd=retry_cmd, role=role,
            )
        except SystemExit as exc:
            return inner, None, exc
    return inner, result, None


def test_retry_returns_first_attempt_when_no_filter(streaming: ModuleType) -> None:
    """A clean first attempt returns its result without retrying."""
    inner, result, _ = _run_retry(streaming, ["DONE"])
    assert (result, inner.call_count) == ("DONE", 1)


def test_retry_recovers_after_one_filter(streaming: ModuleType) -> None:
    """One filter strike retries with the recovery prompt and succeeds."""
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 2)


def test_retry_uses_retry_cmd_after_filter(streaming: ModuleType) -> None:
    """The retry call uses the supplied retry_cmd, not the initial cmd."""
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    retry_cmd = ["claude", "--continue", "--marker"]
    inner, _, _ = _run_retry(streaming, side, retry_cmd=retry_cmd)
    assert inner.call_args_list[1][0][0] == retry_cmd


def test_retry_uses_recovery_prompt_after_filter(streaming: ModuleType) -> None:
    """The retry call uses CONTENT_FILTER_RETRY_PROMPT, not the original."""
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    inner, _, _ = _run_retry(streaming, side)
    assert inner.call_args_list[1][0][1] == streaming.CONTENT_FILTER_RETRY_PROMPT


def test_retry_recovery_prompt_mentions_copyright(streaming: ModuleType) -> None:
    """The recovery prompt names the LRM copyright reason."""
    assert "copyright" in streaming.CONTENT_FILTER_RETRY_PROMPT.lower()


def test_retry_succeeds_after_two_strikes(streaming: ModuleType) -> None:
    """Two filter strikes followed by success returns the final result."""
    side = [
        streaming.ContentFilterError("blocked"),
        streaming.ContentFilterError("blocked"),
        "DONE",
    ]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 3)


def test_retry_exits_after_max_retries(streaming: ModuleType) -> None:
    """Three filter strikes (initial + two retries) exits non-zero."""
    side = [streaming.ContentFilterError("blocked")] * 3
    _, _, exc = _run_retry(streaming, side)
    assert exc is not None


def test_retry_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error names the caller's role."""
    side = [streaming.ContentFilterError("blocked")] * 3
    _run_retry(streaming, side, role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_retry_warning_includes_attempt_number(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Each retry prints a warning naming the attempt number."""
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    _run_retry(streaming, side)
    assert "attempt 1" in capsys.readouterr().err


# --- MissingResultEventError + run_claude_streaming -------------------------


def test_missing_result_event_error_is_exception(streaming: ModuleType) -> None:
    """MissingResultEventError is exposed as an Exception subclass."""
    assert issubclass(streaming.MissingResultEventError, Exception)


def test_missing_result_session_id_captured_from_system_event(
    streaming: ModuleType,
) -> None:
    """The session_id from the first system event is captured on the exception."""
    lines = [
        '{"type":"system","subtype":"init","session_id":"sid-abc-123"}\n',
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert exc.session_id == "sid-abc-123"


def test_missing_result_session_id_is_none_without_system_event(
    streaming: ModuleType,
) -> None:
    """session_id is None when no system event arrived."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert exc.session_id is None


def test_missing_result_session_id_ignores_non_string(streaming: ModuleType) -> None:
    """A non-string session_id field on the system event is treated as missing."""
    lines = [
        '{"type":"system","session_id":42}\n',
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert exc.session_id is None


def test_missing_result_last_event_after_tool_result_names_tool(
    streaming: ModuleType,
) -> None:
    """A stream ending after a tool_result identifies the tool by name."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"tool_use","name":"TodoWrite","input":{}}]}}\n',
        '{"type":"user","message":{"content":'
        '[{"type":"tool_result","content":"ok"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "TodoWrite" in exc.last_event


def test_missing_result_last_event_after_assistant_text(streaming: ModuleType) -> None:
    """A stream ending after assistant text describes that as the last event."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "text" in exc.last_event


def test_missing_result_last_event_after_assistant_thinking(streaming: ModuleType) -> None:
    """A stream ending after a thinking block describes that as the last event."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"thinking","text":"..."}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "thinking" in exc.last_event


def test_missing_result_last_event_after_assistant_tool_use(streaming: ModuleType) -> None:
    """A stream ending after a tool_use identifies the tool by name."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"tool_use","name":"Read","input":{"file_path":"/x"}}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "Read" in exc.last_event


def test_missing_result_last_event_when_no_events_seen(streaming: ModuleType) -> None:
    """An empty stream still yields a non-empty last_event description."""
    exc = _run_capturing_missing_result(streaming, [])
    assert exc.last_event


def test_missing_result_str_includes_session_id(streaming: ModuleType) -> None:
    """str(exception) includes the session id for log correlation."""
    lines = [
        '{"type":"system","subtype":"init","session_id":"sid-abc-123"}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "sid-abc-123" in str(exc)


def test_missing_result_str_includes_last_event(streaming: ModuleType) -> None:
    """str(exception) includes the last_event description."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"tool_use","name":"TodoWrite","input":{}}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "TodoWrite" in str(exc)


# --- run_claude_streaming_with_retry: missing-result retry ------------------


def _missing_result(streaming: ModuleType, **kwargs: Any) -> Any:
    """Construct a MissingResultEventError with sensible defaults."""
    defaults: dict[str, Any] = {
        "session_id": None, "last_event": "x", "stderr": "",
    }
    defaults.update(kwargs)
    return streaming.MissingResultEventError(**defaults)


def test_missing_result_retry_recovers_after_one_strike(streaming: ModuleType) -> None:
    """One missing-result strike retries with the recovery prompt and succeeds."""
    side = [_missing_result(streaming), "DONE"]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 2)


def test_missing_result_retry_uses_retry_cmd(streaming: ModuleType) -> None:
    """The retry call uses the supplied retry_cmd, not the initial cmd."""
    side = [_missing_result(streaming), "DONE"]
    retry_cmd = ["claude", "--continue", "--marker"]
    inner, _, _ = _run_retry(streaming, side, retry_cmd=retry_cmd)
    assert inner.call_args_list[1][0][0] == retry_cmd


def test_missing_result_retry_uses_recovery_prompt(streaming: ModuleType) -> None:
    """The retry call uses MISSING_RESULT_RETRY_PROMPT, not the original."""
    side = [_missing_result(streaming), "DONE"]
    inner, _, _ = _run_retry(streaming, side)
    assert (
        inner.call_args_list[1][0][1]
        == streaming.MISSING_RESULT_RETRY_PROMPT
    )


def test_missing_result_retry_recovery_prompt_mentions_continue(
    streaming: ModuleType,
) -> None:
    """The recovery prompt explains the previous stream ended without a result."""
    assert "result" in streaming.MISSING_RESULT_RETRY_PROMPT.lower()


def test_missing_result_retry_exits_after_max_strikes(streaming: ModuleType) -> None:
    """Two missing-result strikes (initial + one retry) exit non-zero."""
    side = [_missing_result(streaming)] * 2
    _, _, exc = _run_retry(streaming, side)
    assert exc is not None


def test_missing_result_retry_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error names the caller's role on missing-result exhaust."""
    side = [_missing_result(streaming)] * 2
    _run_retry(streaming, side, role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_missing_result_retry_exit_message_includes_session_id(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error includes session_id for log correlation."""
    side = [_missing_result(streaming, session_id="sid-99")] * 2
    _run_retry(streaming, side)
    assert "sid-99" in capsys.readouterr().err


def test_missing_result_retry_exit_message_includes_last_event(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error includes last_event for diagnostic context."""
    side = [
        _missing_result(streaming, last_event="tool_result for TodoWrite"),
    ] * 2
    _run_retry(streaming, side)
    assert "TodoWrite" in capsys.readouterr().err


def test_missing_result_retry_exit_dumps_stderr(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error dumps the captured stderr from the last attempt."""
    side = [
        _missing_result(streaming, stderr="UNIQUE_EXHAUST_STDERR"),
    ] * 2
    _run_retry(streaming, side)
    assert "UNIQUE_EXHAUST_STDERR" in capsys.readouterr().err


def test_missing_result_retry_warning_includes_session_id(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The retry warning includes session_id for log correlation."""
    side = [_missing_result(streaming, session_id="sid-77"), "DONE"]
    _run_retry(streaming, side)
    assert "sid-77" in capsys.readouterr().err


def test_missing_result_retry_warning_includes_last_event(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The retry warning includes last_event for diagnostic context."""
    side = [
        _missing_result(
            streaming, last_event="tool_result for TodoWrite",
        ),
        "DONE",
    ]
    _run_retry(streaming, side)
    assert "TodoWrite" in capsys.readouterr().err


def test_filter_and_missing_result_have_independent_budgets(streaming: ModuleType) -> None:
    """Each error type tracks its own attempt counter; mixed strikes recover."""
    side = [
        streaming.ContentFilterError("blocked"),
        _missing_result(streaming),
        "DONE",
    ]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 3)
