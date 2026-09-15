import io
import os
from collections.abc import Callable
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest


def test_extract_result_returns_text(streaming: ModuleType) -> None:
    assert streaming.extract_result(
        {"type": "result", "result": "done"},
    ) == "done"


def test_extract_result_non_result_event(streaming: ModuleType) -> None:
    assert streaming.extract_result({"type": "assistant"}) is None


def test_extract_result_empty_string(streaming: ModuleType) -> None:
    assert streaming.extract_result(
        {"type": "result", "result": ""},
    ) is None


def test_extract_result_non_string(streaming: ModuleType) -> None:
    assert streaming.extract_result(
        {"type": "result", "result": 42},
    ) is None


def test_extract_result_missing(streaming: ModuleType) -> None:
    assert streaming.extract_result({"type": "result"}) is None


def test_build_streaming_cmd_starts_with_claude(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert cmd[:2] == ["claude", "-p"]


def test_build_streaming_cmd_carries_model(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(model="haiku", settings_path="/tmp/s")
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_build_streaming_cmd_uses_stream_json(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_build_streaming_cmd_uses_verbose(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--verbose" in cmd


def test_build_streaming_cmd_uses_dangerously_skip_permissions(
    streaming: ModuleType,
) -> None:
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--dangerously-skip-permissions" in cmd


def test_build_streaming_cmd_carries_settings_path(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(
        model="opus", settings_path="/tmp/deny.json",
    )
    assert cmd[cmd.index("--settings") + 1] == "/tmp/deny.json"


def test_build_streaming_cmd_omits_disallowed_tools_flag(
    streaming: ModuleType,
) -> None:
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--disallowedTools" not in cmd


def test_build_streaming_cmd_carries_effort(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(
        model="opus", settings_path="/tmp/s", effort="medium",
    )
    assert cmd[cmd.index("--effort") + 1] == "medium"


def test_build_streaming_cmd_omits_effort_by_default(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(model="opus", settings_path="/tmp/s")
    assert "--effort" not in cmd


def test_build_streaming_cmd_appends_continue(streaming: ModuleType) -> None:
    cmd = streaming.build_streaming_cmd(
        model="opus", settings_path="/tmp/s", continue_session=True,
    )
    assert "--continue" in cmd


def _first_hook_cmd(settings: dict[str, Any]) -> str:
    cmd: str = settings["hooks"]["PreToolUse"][0]["hooks"][0]["command"]
    return cmd


def test_write_deny_hook_settings_returns_existing_path(
    streaming: ModuleType,
) -> None:
    path = streaming.write_deny_hook_settings(["cmake"])
    try:
        assert os.path.exists(path)
    finally:
        os.unlink(path)


def test_write_deny_hook_settings_installs_pretooluse_hook(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    assert "PreToolUse" in make_settings(["cmake"])["hooks"]


def test_write_deny_hook_settings_disables_auto_memory(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    assert make_settings(["cmake"])["autoMemoryEnabled"] is False


def test_write_deny_hook_settings_matches_bash(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    settings = make_settings(["cmake"])
    assert settings["hooks"]["PreToolUse"][0]["matcher"] == "Bash"


def test_write_deny_hook_settings_command_carries_first_pattern(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    assert "cmake" in _first_hook_cmd(make_settings(["cmake", "make"]))


def test_write_deny_hook_settings_command_carries_second_pattern(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    assert "make" in _first_hook_cmd(make_settings(["cmake", "make"]))


def test_write_deny_hook_settings_command_references_hook_script(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    assert "deny_bash_hook.py" in _first_hook_cmd(make_settings(["cmake"]))


def test_write_deny_hook_settings_quotes_patterns_with_spaces(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    assert "'git commit'" in _first_hook_cmd(make_settings(["git commit"]))


def test_write_deny_hook_settings_hook_type_is_command(
    make_settings: Callable[[list[str]], dict[str, Any]],
) -> None:
    settings = make_settings(["cmake"])
    assert settings["hooks"]["PreToolUse"][0]["hooks"][0]["type"] == "command"


def _make_proc(
    stdout_lines: list[str], *, stderr: str = "", returncode: int = 0,
) -> tuple[MagicMock, MagicMock]:
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
    assert _run(streaming, _OK_STREAM)[0] == "final"


def test_run_claude_streaming_writes_prompt(streaming: ModuleType) -> None:
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.write.call_args == (("prompt",),)


def test_run_claude_streaming_closes_stdin(streaming: ModuleType) -> None:
    _, _, proc = _run(streaming, _OK_STREAM)
    assert proc.stdin.close.call_count == 1


def test_run_claude_streaming_passes_env(streaming: ModuleType) -> None:
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[1]["env"] == {"PATH": "/usr/bin"}


def test_run_claude_streaming_passes_cmd(streaming: ModuleType) -> None:
    _, popen, _ = _run(streaming, _OK_STREAM)
    assert popen.call_args[0][0] == ["claude"]


def test_run_claude_streaming_prints_assistant_text(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _run(streaming, _OK_STREAM)
    assert "hi" in capsys.readouterr().out


def test_run_claude_streaming_skips_blank_lines(streaming: ModuleType) -> None:
    lines = ["\n", "   \n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_skips_non_json_lines(streaming: ModuleType) -> None:
    lines = ["not json\n"] + _OK_STREAM
    assert _run(streaming, lines)[0] == "final"


def test_run_claude_streaming_exits_on_nonzero(streaming: ModuleType) -> None:
    with pytest.raises(SystemExit):
        _run(streaming, _OK_STREAM, returncode=1, stderr="boom")


def test_run_claude_streaming_dumps_stderr_on_nonzero(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    try:
        _run(streaming, _OK_STREAM, returncode=1, stderr="UNIQUE_STDERR")
    except SystemExit:
        pass
    assert "UNIQUE_STDERR" in capsys.readouterr().err


def test_run_claude_streaming_raises_missing_result_event(streaming: ModuleType) -> None:
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    with pytest.raises(streaming.MissingResultEventError):
        _run(streaming, lines)


def _run_capturing_missing_result(
    streaming: ModuleType, lines: list[str], *, stderr: str = "",
) -> Any:
    try:
        _run(streaming, lines, stderr=stderr)
    except streaming.MissingResultEventError as exc:
        return exc
    raise RuntimeError("expected MissingResultEventError, got success")


def test_run_claude_streaming_missing_result_carries_stderr(streaming: ModuleType) -> None:
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(
        streaming, lines, stderr="UNIQUE_NORESULT_STDERR",
    )
    assert exc.stderr == "UNIQUE_NORESULT_STDERR"


def test_content_filter_error_is_exception(streaming: ModuleType) -> None:
    assert issubclass(streaming.ContentFilterError, Exception)


def test_extract_error_result_returns_none_for_non_result(streaming: ModuleType) -> None:
    assert streaming.extract_error_result({"type": "assistant"}) is None


def test_extract_error_result_returns_none_for_success_result(
    streaming: ModuleType,
) -> None:
    assert streaming.extract_error_result(
        {"type": "result", "result": "ok"},
    ) is None


def test_extract_error_result_describes_subtype(streaming: ModuleType) -> None:
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
        "errors": ["upstream went sideways"],
    })
    assert "error_api" in text


def test_extract_error_result_describes_errors(streaming: ModuleType) -> None:
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
        "errors": ["upstream went sideways"],
    })
    assert "upstream went sideways" in text


def test_extract_error_result_handles_missing_errors(streaming: ModuleType) -> None:
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
    })
    assert "error_api" in text


def test_extract_error_result_handles_non_list_errors(streaming: ModuleType) -> None:
    text = streaming.extract_error_result({
        "type": "result",
        "subtype": "error_api",
        "is_error": True,
        "errors": "scalar error body",
    })
    assert "scalar error body" in text


_ERROR_RESULT_LINE = (
    '{"type":"result","subtype":"error_api","is_error":true,'
    '"errors":["upstream blew up"]}\n'
)


def test_run_claude_streaming_exits_on_error_result(streaming: ModuleType) -> None:
    with pytest.raises(SystemExit):
        _run(streaming, [_ERROR_RESULT_LINE])


def test_run_claude_streaming_error_result_message_includes_subtype(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    try:
        _run(streaming, [_ERROR_RESULT_LINE])
    except SystemExit:
        pass
    assert "error_api" in capsys.readouterr().err


def test_run_claude_streaming_error_result_message_includes_errors(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    try:
        _run(streaming, [_ERROR_RESULT_LINE])
    except SystemExit:
        pass
    assert "upstream blew up" in capsys.readouterr().err


def test_run_claude_streaming_raises_on_raw_content_filter_marker(
    streaming: ModuleType,
) -> None:
    lines = [
        "diagnostic: blocked by content filtering policy\n",
    ]
    with pytest.raises(streaming.ContentFilterError):
        _run(streaming, lines)


def test_run_claude_streaming_raises_on_content_filter_in_error_result(
    streaming: ModuleType,
) -> None:
    lines = [
        '{"type":"result","subtype":"error_api","is_error":true,'
        '"errors":["response was blocked by content filtering"]}\n',
    ]
    with pytest.raises(streaming.ContentFilterError):
        _run(streaming, lines)


def test_run_claude_streaming_raises_on_stderr_content_filter(
    streaming: ModuleType,
) -> None:
    with pytest.raises(streaming.ContentFilterError):
        _run(
            streaming,
            _OK_STREAM,
            returncode=1,
            stderr="message blocked by content filtering",
        )


def _run_retry(
    streaming: ModuleType, side_effects: list[Any],
    *, role: str = "Step", retry_cmd: list[str] | None = None,
) -> tuple[MagicMock, Any, SystemExit | None]:
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
    inner, result, _ = _run_retry(streaming, ["DONE"])
    assert (result, inner.call_count) == ("DONE", 1)


def test_retry_recovers_after_one_filter(streaming: ModuleType) -> None:
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 2)


def test_retry_uses_retry_cmd_after_filter(streaming: ModuleType) -> None:
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    retry_cmd = ["claude", "--continue", "--marker"]
    inner, _, _ = _run_retry(streaming, side, retry_cmd=retry_cmd)
    assert inner.call_args_list[1][0][0] == retry_cmd


def test_retry_uses_recovery_prompt_after_filter(streaming: ModuleType) -> None:
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    inner, _, _ = _run_retry(streaming, side)
    assert inner.call_args_list[1][0][1] == streaming.CONTENT_FILTER_RETRY_PROMPT


def test_retry_recovery_prompt_mentions_copyright(streaming: ModuleType) -> None:
    assert "copyright" in streaming.CONTENT_FILTER_RETRY_PROMPT.lower()


def test_retry_succeeds_after_two_strikes(streaming: ModuleType) -> None:
    side = [
        streaming.ContentFilterError("blocked"),
        streaming.ContentFilterError("blocked"),
        "DONE",
    ]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 3)


def test_retry_exits_after_max_retries(streaming: ModuleType) -> None:
    side = [streaming.ContentFilterError("blocked")] * 3
    _, _, exc = _run_retry(streaming, side)
    assert exc is not None


def test_retry_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [streaming.ContentFilterError("blocked")] * 3
    _run_retry(streaming, side, role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_retry_warning_includes_attempt_number(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [streaming.ContentFilterError("blocked"), "DONE"]
    _run_retry(streaming, side)
    assert "attempt 1" in capsys.readouterr().err


def test_missing_result_event_error_is_exception(streaming: ModuleType) -> None:
    assert issubclass(streaming.MissingResultEventError, Exception)


def test_missing_result_session_id_captured_from_system_event(
    streaming: ModuleType,
) -> None:
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
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert exc.session_id is None


def test_missing_result_session_id_ignores_non_string(streaming: ModuleType) -> None:
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
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"tool_use","name":"TodoWrite","input":{}}]}}\n',
        '{"type":"user","message":{"content":'
        '[{"type":"tool_result","content":"ok"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "TodoWrite" in exc.last_event


def test_missing_result_last_event_after_assistant_text(streaming: ModuleType) -> None:
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"text","text":"hi"}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "text" in exc.last_event


def test_missing_result_last_event_after_assistant_thinking(streaming: ModuleType) -> None:
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"thinking","text":"..."}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "thinking" in exc.last_event


def test_missing_result_last_event_after_assistant_tool_use(streaming: ModuleType) -> None:
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"tool_use","name":"Read","input":{"file_path":"/x"}}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "Read" in exc.last_event


def test_missing_result_last_event_when_no_events_seen(streaming: ModuleType) -> None:
    exc = _run_capturing_missing_result(streaming, [])
    assert exc.last_event


def test_missing_result_str_includes_session_id(streaming: ModuleType) -> None:
    lines = [
        '{"type":"system","subtype":"init","session_id":"sid-abc-123"}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "sid-abc-123" in str(exc)


def test_missing_result_str_includes_last_event(streaming: ModuleType) -> None:
    lines = [
        '{"type":"assistant","message":{"content":'
        '[{"type":"tool_use","name":"TodoWrite","input":{}}]}}\n',
    ]
    exc = _run_capturing_missing_result(streaming, lines)
    assert "TodoWrite" in str(exc)


def _missing_result(streaming: ModuleType, **kwargs: Any) -> Any:
    defaults: dict[str, Any] = {
        "session_id": None, "last_event": "x", "stderr": "",
    }
    defaults.update(kwargs)
    return streaming.MissingResultEventError(**defaults)


def test_missing_result_retry_recovers_after_one_strike(streaming: ModuleType) -> None:
    side = [_missing_result(streaming), "DONE"]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 2)


def test_missing_result_retry_uses_retry_cmd(streaming: ModuleType) -> None:
    side = [_missing_result(streaming), "DONE"]
    retry_cmd = ["claude", "--continue", "--marker"]
    inner, _, _ = _run_retry(streaming, side, retry_cmd=retry_cmd)
    assert inner.call_args_list[1][0][0] == retry_cmd


def test_missing_result_retry_uses_recovery_prompt(streaming: ModuleType) -> None:
    side = [_missing_result(streaming), "DONE"]
    inner, _, _ = _run_retry(streaming, side)
    assert (
        inner.call_args_list[1][0][1]
        == streaming.MISSING_RESULT_RETRY_PROMPT
    )


def test_missing_result_retry_recovery_prompt_mentions_continue(
    streaming: ModuleType,
) -> None:
    assert "result" in streaming.MISSING_RESULT_RETRY_PROMPT.lower()


def test_missing_result_retry_exits_after_max_strikes(streaming: ModuleType) -> None:
    side = [_missing_result(streaming)] * 2
    _, _, exc = _run_retry(streaming, side)
    assert exc is not None


def test_missing_result_retry_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [_missing_result(streaming)] * 2
    _run_retry(streaming, side, role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_missing_result_retry_exit_message_includes_session_id(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [_missing_result(streaming, session_id="sid-99")] * 2
    _run_retry(streaming, side)
    assert "sid-99" in capsys.readouterr().err


def test_missing_result_retry_exit_message_includes_last_event(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [
        _missing_result(streaming, last_event="tool_result for TodoWrite"),
    ] * 2
    _run_retry(streaming, side)
    assert "TodoWrite" in capsys.readouterr().err


def test_missing_result_retry_exit_dumps_stderr(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [
        _missing_result(streaming, stderr="UNIQUE_EXHAUST_STDERR"),
    ] * 2
    _run_retry(streaming, side)
    assert "UNIQUE_EXHAUST_STDERR" in capsys.readouterr().err


def test_missing_result_retry_warning_includes_session_id(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [_missing_result(streaming, session_id="sid-77"), "DONE"]
    _run_retry(streaming, side)
    assert "sid-77" in capsys.readouterr().err


def test_missing_result_retry_warning_includes_last_event(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [
        _missing_result(
            streaming, last_event="tool_result for TodoWrite",
        ),
        "DONE",
    ]
    _run_retry(streaming, side)
    assert "TodoWrite" in capsys.readouterr().err


def test_filter_and_missing_result_have_independent_budgets(streaming: ModuleType) -> None:
    side = [
        streaming.ContentFilterError("blocked"),
        _missing_result(streaming),
        "DONE",
    ]
    inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 3)


_SOCKET_STDERR = "API Error: the socket connection was closed unexpectedly"

_OVERLOAD_STDOUT = (
    "API Error: 529 Overloaded. This is a server-side issue, usually"
    " temporary — try again in a moment. If it persists, check"
    " https://status.claude.com."
)


def test_transient_network_error_carries_stderr(streaming: ModuleType) -> None:
    assert streaming.TransientNetworkError("boom").stderr == "boom"


def test_max_network_retries_matches_attempt_budget(streaming: ModuleType) -> None:
    assert streaming.MAX_NETWORK_RETRIES == streaming.DEFAULT_MAX_ATTEMPTS


def test_run_claude_streaming_raises_transient_on_stderr_marker(
    streaming: ModuleType,
) -> None:
    with pytest.raises(streaming.TransientNetworkError):
        _run(streaming, _OK_STREAM, returncode=1, stderr=_SOCKET_STDERR)


def test_run_claude_streaming_raises_transient_on_stream_marker(
    streaming: ModuleType,
) -> None:
    lines = [_SOCKET_STDERR + "\n"] + _OK_STREAM
    with pytest.raises(streaming.TransientNetworkError):
        _run(streaming, lines, returncode=1, stderr="")


def test_run_claude_streaming_raises_transient_on_overload_marker(
    streaming: ModuleType,
) -> None:
    lines = [_OVERLOAD_STDOUT + "\n"] + _OK_STREAM
    with pytest.raises(streaming.TransientNetworkError):
        _run(streaming, lines, returncode=1, stderr="")


def test_run_claude_streaming_transient_carries_stderr(
    streaming: ModuleType,
) -> None:
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
    side: list[Any] = [streaming.TransientNetworkError("NET_STDERR")] * strikes
    side += trailing if trailing is not None else ["DONE"]
    with patch.object(streaming, "sleep_before_retry") as sleep:
        inner, result, exc = _run_retry(streaming, side, retry_cmd=retry_cmd)
    return inner, result, exc, sleep


def test_retry_recovers_after_one_network_error(streaming: ModuleType) -> None:
    inner, result, _, _ = _run_network_retry(streaming, 1)
    assert (result, inner.call_count) == ("DONE", 2)


def test_retry_sleeps_once_after_one_network_error(streaming: ModuleType) -> None:
    _, _, _, sleep = _run_network_retry(streaming, 1)
    assert sleep.call_count == 1


def test_retry_network_first_backoff_uses_attempt_zero(streaming: ModuleType) -> None:
    _, _, _, sleep = _run_network_retry(streaming, 1)
    assert sleep.call_args_list[0][0][0] == 0


def test_retry_network_last_backoff_reaches_two_pow_nine(
    streaming: ModuleType,
) -> None:
    _, _, _, sleep = _run_network_retry(streaming, streaming.MAX_NETWORK_RETRIES)
    assert sleep.call_args_list[-1][0][0] == streaming.DEFAULT_MAX_ATTEMPTS - 1


def test_retry_network_reuses_original_cmd(streaming: ModuleType) -> None:
    retry_cmd = ["claude", "--continue", "--marker"]
    inner, _, _, _ = _run_network_retry(streaming, 1, retry_cmd=retry_cmd)
    assert inner.call_args_list[1][0][0] == ["claude"]


def test_retry_network_reuses_original_prompt(streaming: ModuleType) -> None:
    inner, _, _, _ = _run_network_retry(streaming, 1)
    assert inner.call_args_list[1][0][1] == "orig"


def test_retry_network_warning_includes_attempt_number(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _run_network_retry(streaming, 1)
    assert "attempt 1" in capsys.readouterr().err


def test_retry_network_exits_after_budget(streaming: ModuleType) -> None:
    _, _, exc, _ = _run_network_retry(
        streaming, streaming.MAX_NETWORK_RETRIES + 1, trailing=[],
    )
    assert exc is not None


def test_retry_network_makes_eleven_calls_before_exit(streaming: ModuleType) -> None:
    inner, _, _, _ = _run_network_retry(
        streaming, streaming.MAX_NETWORK_RETRIES + 1, trailing=[],
    )
    assert inner.call_count == streaming.MAX_NETWORK_RETRIES + 1


def test_retry_network_exit_dumps_stderr(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    _run_network_retry(streaming, streaming.MAX_NETWORK_RETRIES + 1, trailing=[])
    assert "NET_STDERR" in capsys.readouterr().err


def test_retry_network_exit_message_names_role(
    streaming: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    side = [streaming.TransientNetworkError("x")] * (streaming.MAX_NETWORK_RETRIES + 1)
    with patch.object(streaming, "sleep_before_retry"):
        _run_retry(streaming, side, role="Oracle")
    assert "Oracle" in capsys.readouterr().err


def test_network_and_filter_have_independent_budgets(streaming: ModuleType) -> None:
    side = [
        streaming.TransientNetworkError("x"),
        streaming.ContentFilterError("blocked"),
        "DONE",
    ]
    with patch.object(streaming, "sleep_before_retry"):
        inner, result, _ = _run_retry(streaming, side)
    assert (result, inner.call_count) == ("DONE", 3)
