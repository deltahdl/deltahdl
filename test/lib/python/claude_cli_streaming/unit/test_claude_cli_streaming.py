"""Unit tests for the subprocess runner in lib.python.claude_cli_streaming."""

import io
import os
from collections.abc import Callable
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest


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
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert cmd[:2] == ["claude", "-p"]


def test_build_streaming_cmd_carries_model(streaming: ModuleType) -> None:
    """The model argument is forwarded to --model."""
    cmd = streaming.build_streaming_cmd(model="haiku", settings_path="/tmp/s")
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_build_streaming_cmd_uses_stream_json(streaming: ModuleType) -> None:
    """--output-format stream-json is set so events stream live."""
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_build_streaming_cmd_uses_verbose(streaming: ModuleType) -> None:
    """--verbose is required for stream-json output."""
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--verbose" in cmd


def test_build_streaming_cmd_uses_dangerously_skip_permissions(
    streaming: ModuleType,
) -> None:
    """--dangerously-skip-permissions stays so every non-Bash tool auto-approves."""
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--dangerously-skip-permissions" in cmd


def test_build_streaming_cmd_carries_settings_path(streaming: ModuleType) -> None:
    """The settings path is forwarded to --settings."""
    cmd = streaming.build_streaming_cmd(
        model="opus", settings_path="/tmp/deny.json",
    )
    assert cmd[cmd.index("--settings") + 1] == "/tmp/deny.json"


def test_build_streaming_cmd_omits_disallowed_tools_flag(
    streaming: ModuleType,
) -> None:
    """The legacy --disallowedTools flag is no longer emitted."""
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--disallowedTools" not in cmd


def test_build_streaming_cmd_carries_effort(streaming: ModuleType) -> None:
    """An effort kwarg is forwarded to --effort."""
    cmd = streaming.build_streaming_cmd(
        model="opus", settings_path="/tmp/s", effort="medium",
    )
    assert cmd[cmd.index("--effort") + 1] == "medium"


def test_build_streaming_cmd_omits_effort_by_default(streaming: ModuleType) -> None:
    """Without an effort kwarg, --effort is not present in the argv."""
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--effort" not in cmd


def test_build_streaming_cmd_appends_continue(streaming: ModuleType) -> None:
    """continue_session=True appends --continue to the argv."""
    cmd = streaming.build_streaming_cmd(
        model="opus", settings_path="/tmp/s", continue_session=True,
    )
    assert "--continue" in cmd


# --- write_deny_hook_settings -----------------------------------------------


def _first_hook_cmd(settings: dict[str, Any]) -> str:
    """Return the command string from the first PreToolUse hook."""
    cmd: str = settings["hooks"]["PreToolUse"][0]["hooks"][0]["command"]
    return cmd


def test_write_deny_hook_settings_returns_existing_path(
    streaming: ModuleType,
) -> None:
    """The returned path points at an actual file."""
    path = streaming.write_deny_hook_settings(["cmake"])
    try:
        assert os.path.exists(path)
    finally:
        os.unlink(path)


def test_write_deny_hook_settings_installs_pretooluse_hook(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """The settings install a PreToolUse hook."""
    assert "PreToolUse" in make_settings(["cmake"])["hooks"]


def test_write_deny_hook_settings_matches_bash(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """The PreToolUse hook matches Bash tool calls."""
    settings = make_settings(["cmake"])
    assert settings["hooks"]["PreToolUse"][0]["matcher"] == "Bash"


def test_write_deny_hook_settings_command_carries_first_pattern(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """The first deny pattern is embedded in the hook command argv."""
    assert "cmake" in _first_hook_cmd(make_settings(["cmake", "make"]))


def test_write_deny_hook_settings_command_carries_second_pattern(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """The second deny pattern is also embedded in the hook command argv."""
    assert "make" in _first_hook_cmd(make_settings(["cmake", "make"]))


def test_write_deny_hook_settings_command_references_hook_script(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """The hook command references the deny_bash_hook.py script."""
    assert "deny_bash_hook.py" in _first_hook_cmd(make_settings(["cmake"]))


def test_write_deny_hook_settings_quotes_patterns_with_spaces(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """Patterns containing spaces are shell-quoted in the hook command."""
    assert "'git commit'" in _first_hook_cmd(make_settings(["git commit"]))


def test_write_deny_hook_settings_hook_type_is_command(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    """The hook entry is typed as a command hook."""
    settings = make_settings(["cmake"])
    assert settings["hooks"]["PreToolUse"][0]["hooks"][0]["type"] == "command"


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
        "lib.python.claude_cli_streaming.subprocess.Popen",
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


# --- transient network errors -----------------------------------------------


_SOCKET_STDERR = "API Error: the socket connection was closed unexpectedly"

# The exact line the Claude CLI prints to stdout on a server-side 529, observed
# during a satisfy_subclauses run: text on stdout, exit code 1, empty stderr.
_OVERLOAD_STDOUT = (
    "API Error: 529 Overloaded. This is a server-side issue, usually"
    " temporary — try again in a moment. If it persists, check"
    " https://status.claude.com."
)


def test_transient_network_error_carries_stderr(streaming: ModuleType) -> None:
    """The exception preserves the CLI stderr for the loud-fatal."""
    assert streaming.TransientNetworkError("boom").stderr == "boom"


def test_max_network_retries_matches_attempt_budget(streaming: ModuleType) -> None:
    """The network budget spans the full shared attempt budget (backoff up to 2^9)."""
    assert streaming.MAX_NETWORK_RETRIES == streaming.DEFAULT_MAX_ATTEMPTS


def test_run_claude_streaming_raises_transient_on_stderr_marker(
    streaming: ModuleType,
) -> None:
    """A non-zero exit with a socket marker in stderr raises TransientNetworkError."""
    with pytest.raises(streaming.TransientNetworkError):
        _run(streaming, _OK_STREAM, returncode=1, stderr=_SOCKET_STDERR)


def test_run_claude_streaming_raises_transient_on_stream_marker(
    streaming: ModuleType,
) -> None:
    """A socket marker on a streamed line raises even when stderr is empty."""
    lines = [_SOCKET_STDERR + "\n"] + _OK_STREAM
    with pytest.raises(streaming.TransientNetworkError):
        _run(streaming, lines, returncode=1, stderr="")


def test_run_claude_streaming_raises_transient_on_overload_marker(
    streaming: ModuleType,
) -> None:
    """A 529 Overloaded stdout line with exit 1 and empty stderr is recoverable."""
    lines = [_OVERLOAD_STDOUT + "\n"] + _OK_STREAM
    with pytest.raises(streaming.TransientNetworkError):
        _run(streaming, lines, returncode=1, stderr="")


def test_run_claude_streaming_transient_carries_stderr(
    streaming: ModuleType,
) -> None:
    """The raised TransientNetworkError carries the captured stderr."""
    captured = None
    try:
        _run(streaming, _OK_STREAM, returncode=1, stderr=_SOCKET_STDERR)
    except streaming.TransientNetworkError as exc:
        captured = exc.stderr
    assert captured == _SOCKET_STDERR


def _run_network_retry(
    streaming: ModuleType, strikes: int, *, trailing: list[Any] | None = None,
    retry_cmd: list[str] | None = None,
) -> tuple[MagicMock, Any, SystemExit | None, MagicMock]:
    """Drive the retry wrapper with *strikes* TransientNetworkErrors, sleep stubbed."""
    side: list[Any] = [streaming.TransientNetworkError("NET_STDERR")] * strikes
    side += trailing if trailing is not None else ["DONE"]
    with patch.object(streaming, "sleep_before_retry") as sleep:
        inner, result, exc = _run_retry(streaming, side, retry_cmd=retry_cmd)
    return inner, result, exc, sleep


def test_retry_recovers_after_one_network_error(streaming: ModuleType) -> None:
    """One transient network strike then success returns the result in two calls."""
    inner, result, _, _ = _run_network_retry(streaming, 1)
    assert (result, inner.call_count) == ("DONE", 2)


def test_retry_sleeps_once_after_one_network_error(streaming: ModuleType) -> None:
    """One transient network strike causes exactly one backoff sleep."""
    _, _, _, sleep = _run_network_retry(streaming, 1)
    assert sleep.call_count == 1


def test_retry_network_first_backoff_uses_attempt_zero(streaming: ModuleType) -> None:
    """The first retry backs off with attempt index 0 (up to 1s)."""
    _, _, _, sleep = _run_network_retry(streaming, 1)
    assert sleep.call_args_list[0][0][0] == 0


def test_retry_network_last_backoff_reaches_two_pow_nine(
    streaming: ModuleType,
) -> None:
    """The final retry backs off with attempt index 9 (jitter window up to 2^9)."""
    _, _, _, sleep = _run_network_retry(streaming, streaming.MAX_NETWORK_RETRIES)
    assert sleep.call_args_list[-1][0][0] == streaming.DEFAULT_MAX_ATTEMPTS - 1


def test_retry_network_reuses_original_cmd(streaming: ModuleType) -> None:
    """The re-run uses the original cmd, not retry_cmd (--continue is unsafe)."""
    retry_cmd = ["claude", "--continue", "--marker"]
    inner, _, _, _ = _run_network_retry(streaming, 1, retry_cmd=retry_cmd)
    assert inner.call_args_list[1][0][0] == ["claude"]


def test_retry_network_reuses_original_prompt(streaming: ModuleType) -> None:
    """The re-run reuses the original prompt unchanged."""
    inner, _, _, _ = _run_network_retry(streaming, 1)
    assert inner.call_args_list[1][0][1] == "orig"


def test_retry_network_warning_includes_attempt_number(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The retry warning names the attempt number."""
    _run_network_retry(streaming, 1)
    assert "attempt 1" in capsys.readouterr().err


def test_retry_network_exits_after_budget(streaming: ModuleType) -> None:
    """Strikes exceeding the budget exit non-zero."""
    _, _, exc, _ = _run_network_retry(
        streaming, streaming.MAX_NETWORK_RETRIES + 1, trailing=[],
    )
    assert exc is not None


def test_retry_network_makes_eleven_calls_before_exit(streaming: ModuleType) -> None:
    """Persistent transient failure makes initial + MAX_NETWORK_RETRIES inner calls."""
    inner, _, _, _ = _run_network_retry(
        streaming, streaming.MAX_NETWORK_RETRIES + 1, trailing=[],
    )
    assert inner.call_count == streaming.MAX_NETWORK_RETRIES + 1


def test_retry_network_exit_dumps_stderr(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal error dumps the captured network stderr."""
    _run_network_retry(streaming, streaming.MAX_NETWORK_RETRIES + 1, trailing=[])
    assert "NET_STDERR" in capsys.readouterr().err


def test_retry_network_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """The terminal network error names the caller's role."""
    side = [streaming.TransientNetworkError("x")] * (streaming.MAX_NETWORK_RETRIES + 1)
    with patch.object(streaming, "sleep_before_retry"):
        _run_retry(streaming, side, role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_network_and_filter_have_independent_budgets(streaming: ModuleType) -> None:
    """Network and content-filter strikes track separate counters and recover."""
    side = [
        streaming.TransientNetworkError("x"),
        streaming.ContentFilterError("blocked"),
        "DONE",
    ]
    with patch.object(streaming, "sleep_before_retry"):
        inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 3)
