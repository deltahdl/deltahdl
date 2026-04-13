"""Unit tests for implement_subclause._streaming."""

import io
from unittest.mock import MagicMock, patch

import pytest


# ---- _format_tool_call -----------------------------------------------------


def test_format_tool_call_file_path(streaming):
    """file_path is the preferred arg key."""
    block = {"name": "Read", "input": {"file_path": "/tmp/foo.txt"}}
    assert streaming.format_tool_call(block) == "  · Read(/tmp/foo.txt)"


def test_format_tool_call_command(streaming):
    """command is used when file_path is absent."""
    block = {"name": "Bash", "input": {"command": "ls"}}
    assert streaming.format_tool_call(block) == "  · Bash(ls)"


def test_format_tool_call_pattern(streaming):
    """pattern is used for grep-style tools."""
    block = {"name": "Grep", "input": {"pattern": "TODO"}}
    assert streaming.format_tool_call(block) == "  · Grep(TODO)"


def test_format_tool_call_path(streaming):
    """path is used when file_path is absent."""
    block = {"name": "Glob", "input": {"path": "src/"}}
    assert streaming.format_tool_call(block) == "  · Glob(src/)"


def test_format_tool_call_url(streaming):
    """url is used for fetch-style tools."""
    block = {"name": "WebFetch", "input": {"url": "https://example.com"}}
    assert streaming.format_tool_call(block) == "  · WebFetch(https://example.com)"


def test_format_tool_call_query(streaming):
    """query is used for search-style tools."""
    block = {"name": "WebSearch", "input": {"query": "claude"}}
    assert streaming.format_tool_call(block) == "  · WebSearch(claude)"


def test_format_tool_call_no_known_key(streaming):
    """Tools whose input has no recognized key fall back to no-arg form."""
    block = {"name": "Custom", "input": {"foo": "bar"}}
    assert streaming.format_tool_call(block) == "  · Custom()"


def test_format_tool_call_truncates_long_arg(streaming):
    """Arg values longer than 80 chars are truncated with an ellipsis."""
    block = {"name": "Read", "input": {"file_path": "x" * 200}}
    result = streaming.format_tool_call(block)
    assert result.endswith("...)")


def test_format_tool_call_truncated_length(streaming):
    """Truncated arg values stay within the cap including the ellipsis."""
    block = {"name": "Read", "input": {"file_path": "x" * 200}}
    result = streaming.format_tool_call(block)
    assert len(result) == len("  · Read(") + 80 + 1


def test_format_tool_call_missing_name(streaming):
    """A tool_use without a name renders as ?."""
    block = {"input": {"file_path": "/tmp/x"}}
    assert streaming.format_tool_call(block) == "  · ?(/tmp/x)"


def test_format_tool_call_missing_input(streaming):
    """A tool_use without input falls back to the no-arg form."""
    assert streaming.format_tool_call({"name": "Bash"}) == "  · Bash()"


def test_format_tool_call_null_input(streaming):
    """A tool_use with null input falls back to the no-arg form."""
    assert streaming.format_tool_call({"name": "Bash", "input": None}) == "  · Bash()"


# ---- _print_event ----------------------------------------------------------


def test_print_event_assistant_text(streaming, capsys):
    """assistant text blocks are printed verbatim."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "Hello"}]},
    })
    assert "Hello" in capsys.readouterr().out


def test_print_event_assistant_tool_use(streaming, capsys):
    """assistant tool_use blocks are printed as one-line summaries."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [
            {"type": "tool_use", "name": "Read",
             "input": {"file_path": "/x"}},
        ]},
    })
    assert "· Read(/x)" in capsys.readouterr().out


def test_print_event_assistant_skips_whitespace_text(streaming, capsys):
    """assistant text blocks that are whitespace-only are skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text", "text": "   \n"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_skips_unknown_block(streaming, capsys):
    """Unknown block types in an assistant message are silently skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "thinking", "text": "ignored"}]},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_null_content(streaming, capsys):
    """An assistant message with null content prints nothing."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": None},
    })
    assert capsys.readouterr().out == ""


def test_print_event_assistant_null_message(streaming, capsys):
    """An assistant event with null message prints nothing."""
    streaming.print_event({"type": "assistant", "message": None})
    assert capsys.readouterr().out == ""


def test_print_event_non_assistant(streaming, capsys):
    """Non-assistant events are silently ignored."""
    streaming.print_event({"type": "system", "subtype": "init"})
    assert capsys.readouterr().out == ""


def test_print_event_assistant_text_missing_text(streaming, capsys):
    """A text block with no text key is treated as empty and skipped."""
    streaming.print_event({
        "type": "assistant",
        "message": {"content": [{"type": "text"}]},
    })
    assert capsys.readouterr().out == ""


# ---- _extract_result -------------------------------------------------------


def test_extract_result_returns_text(streaming):
    """A result event returns its .result string."""
    assert streaming.extract_result(
        {"type": "result", "result": "done"},
    ) == "done"


def test_extract_result_non_result_event(streaming):
    """Non-result events return None."""
    assert streaming.extract_result({"type": "assistant"}) is None


def test_extract_result_empty_string(streaming):
    """An empty .result returns None."""
    assert streaming.extract_result(
        {"type": "result", "result": ""},
    ) is None


def test_extract_result_non_string(streaming):
    """A non-string .result returns None."""
    assert streaming.extract_result(
        {"type": "result", "result": 42},
    ) is None


def test_extract_result_missing(streaming):
    """A result event with no .result field returns None."""
    assert streaming.extract_result({"type": "result"}) is None


# ---- run_claude_streaming --------------------------------------------------


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
        "implement_subclause.streaming.subprocess.Popen",
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


def test_run_claude_streaming_returns_result(streaming):
    """The terminal result event's .result is returned."""
    assert _run(streaming, _OK_STREAM)[0] == "final"


def test_run_claude_streaming_writes_prompt(streaming):
    """The prompt is written to the child's stdin."""
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.write.call_args == (("prompt",),)


def test_run_claude_streaming_closes_stdin(streaming):
    """stdin is closed after the prompt is written."""
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.close.call_count == 1


def test_run_claude_streaming_passes_env(streaming):
    """The env mapping is forwarded to Popen."""
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[1]["env"] == {"PATH": "/usr/bin"}


def test_run_claude_streaming_passes_cmd(streaming):
    """The command list is forwarded to Popen."""
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[0][0] == ["claude"]


def test_run_claude_streaming_prints_assistant_text(streaming, capsys):
    """Assistant text is streamed to stdout while events arrive."""
    _run(streaming, _OK_STREAM)
    assert "hi" in capsys.readouterr().out


def test_run_claude_streaming_skips_blank_lines(streaming):
    """Blank lines in the stream are skipped without error."""
    lines = ["\n", "   \n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_skips_non_json_lines(streaming):
    """Lines that fail JSON decoding are skipped without error."""
    lines = ["not json\n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_exits_on_nonzero(streaming):
    """A non-zero exit code is loud-fatal."""
    with pytest.raises(SystemExit):
        _run(streaming, _OK_STREAM, returncode=1, stderr="boom")


def test_run_claude_streaming_raises_content_filter_error(streaming):
    """Content filter stderr raises ContentFilterError, not SystemExit."""
    with pytest.raises(streaming.ContentFilterError):
        _run(streaming, _OK_STREAM, returncode=1,
             stderr="Output blocked by content filtering policy")


def test_run_claude_streaming_content_filter_not_system_exit(streaming):
    """Content filter errors do not raise SystemExit."""
    raised_system_exit = False
    try:
        _run(streaming, _OK_STREAM, returncode=1,
             stderr="blocked by content filtering")
    except SystemExit:
        raised_system_exit = True
    except streaming.ContentFilterError:
        pass
    assert not raised_system_exit


def test_run_claude_streaming_dumps_stderr_on_nonzero(streaming, capsys):
    """Non-zero exit dumps stderr to the terminal."""
    try:
        _run(streaming, _OK_STREAM, returncode=1, stderr="UNIQUE_STDERR")
    except SystemExit:
        pass
    assert "UNIQUE_STDERR" in capsys.readouterr().err


def test_run_claude_streaming_exits_when_no_result(streaming):
    """A stream without a terminal result event is loud-fatal."""
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    with pytest.raises(SystemExit):
        _run(streaming, lines)


def test_run_claude_streaming_dumps_stderr_when_no_result(streaming, capsys):
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


# ---- stdout content filter detection ----------------------------------------


_FILTER_STDOUT = [
    'API Error: 400 {"type":"error","error":{"type":'
    '"invalid_request_error","message":'
    '"Output blocked by content filtering policy"}}\n',
]


def test_run_claude_streaming_stdout_content_filter_raises(streaming):
    """Content filter in stdout raises ContentFilterError."""
    with pytest.raises(streaming.ContentFilterError):
        _run(streaming, _FILTER_STDOUT, returncode=1)


def test_run_claude_streaming_stdout_content_filter_not_system_exit(streaming):
    """Content filter in stdout does not raise SystemExit."""
    raised_system_exit = False
    try:
        _run(streaming, _FILTER_STDOUT, returncode=1)
    except SystemExit:
        raised_system_exit = True
    except streaming.ContentFilterError:
        pass
    assert not raised_system_exit
