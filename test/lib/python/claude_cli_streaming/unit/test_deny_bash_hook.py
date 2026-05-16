"""Unit tests for lib.python.claude_cli_streaming.deny_bash_hook."""

import json

from lib.python.claude_cli_streaming import deny_bash_hook as hook


# --- first_tokens -----------------------------------------------------------


def test_first_tokens_empty_command() -> None:
    """An empty command returns an empty list."""
    assert not hook.first_tokens("")


def test_first_tokens_whitespace_only_command() -> None:
    """A whitespace-only command returns an empty list."""
    assert not hook.first_tokens("   \t  ")


def test_first_tokens_single_command() -> None:
    """A single command returns its first token in a single-element list."""
    assert hook.first_tokens("cmake .") == ["cmake"]


def test_first_tokens_and_separator() -> None:
    """`&&` splits subcommands and each first token is collected."""
    assert hook.first_tokens("cd /tmp && cmake .") == ["cd", "cmake"]


def test_first_tokens_or_separator() -> None:
    """`||` splits subcommands."""
    assert hook.first_tokens("make || echo failed") == ["make", "echo"]


def test_first_tokens_semicolon_separator() -> None:
    """`;` splits subcommands."""
    assert hook.first_tokens("cd /tmp; cmake .") == ["cd", "cmake"]


def test_first_tokens_pipe_separator() -> None:
    """A single `|` splits a pipeline."""
    assert hook.first_tokens("ls | grep foo") == ["ls", "grep"]


def test_first_tokens_skips_empty_segments() -> None:
    """Empty subcommands between operators are skipped."""
    assert hook.first_tokens("cmake . ;; make") == ["cmake", "make"]


def test_first_tokens_skips_malformed_segment() -> None:
    """A malformed segment is skipped without dropping later ones."""
    assert hook.first_tokens('"unclosed && cmake .') == ["cmake"]


# --- extract_bash_command ---------------------------------------------------


def _bash_event(command: str) -> str:
    """Build a PreToolUse JSON event for a Bash tool call."""
    return json.dumps({"tool_name": "Bash", "tool_input": {"command": command}})


def test_extract_bash_command_valid_event() -> None:
    """A well-formed Bash event yields its command string."""
    assert hook.extract_bash_command(_bash_event("cmake .")) == "cmake ."


def test_extract_bash_command_invalid_json() -> None:
    """Invalid JSON returns None."""
    assert hook.extract_bash_command("not json") is None


def test_extract_bash_command_non_dict_json() -> None:
    """JSON that isn't an object returns None."""
    assert hook.extract_bash_command("[]") is None


def test_extract_bash_command_non_bash_tool() -> None:
    """An event for a non-Bash tool returns None."""
    payload = json.dumps({"tool_name": "Read", "tool_input": {"file_path": "x"}})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_missing_tool_input() -> None:
    """A Bash event without tool_input returns None."""
    assert hook.extract_bash_command(json.dumps({"tool_name": "Bash"})) is None


def test_extract_bash_command_non_dict_tool_input() -> None:
    """A Bash event whose tool_input isn't an object returns None."""
    payload = json.dumps({"tool_name": "Bash", "tool_input": "cmake ."})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_missing_command() -> None:
    """A Bash event without a command key returns None."""
    payload = json.dumps({"tool_name": "Bash", "tool_input": {}})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_non_string_command() -> None:
    """A Bash event whose command isn't a string returns None."""
    payload = json.dumps({"tool_name": "Bash", "tool_input": {"command": 42}})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_empty_command() -> None:
    """A Bash event with an empty command string returns None."""
    assert hook.extract_bash_command(_bash_event("")) is None


# --- match_deny_pattern -----------------------------------------------------


def test_match_deny_pattern_no_patterns() -> None:
    """An empty deny list never matches."""
    assert hook.match_deny_pattern(_bash_event("cmake ."), []) is None


def test_match_deny_pattern_direct_match() -> None:
    """A first-token match returns (pattern, command)."""
    assert hook.match_deny_pattern(
        _bash_event("cmake ."), ["cmake"],
    ) == ("cmake", "cmake .")


def test_match_deny_pattern_chained_command() -> None:
    """A denied token reached via `&&` is also matched."""
    assert hook.match_deny_pattern(
        _bash_event("cd /tmp && cmake ."), ["cmake"],
    ) == ("cmake", "cd /tmp && cmake .")


def test_match_deny_pattern_no_match() -> None:
    """A command whose tokens are all allowed returns None."""
    assert hook.match_deny_pattern(_bash_event("rm foo"), ["cmake"]) is None


def test_match_deny_pattern_non_bash_event() -> None:
    """A non-Bash event returns None even with patterns set."""
    payload = json.dumps({"tool_name": "Read", "tool_input": {"file_path": "x"}})
    assert hook.match_deny_pattern(payload, ["cmake"]) is None


# --- main -------------------------------------------------------------------


def test_main_allowed_command_exit_code() -> None:
    """An allowed command exits 0."""
    code, _ = hook.main(["hook.py", "cmake"], _bash_event("rm foo"))
    assert code == 0


def test_main_allowed_command_empty_stderr() -> None:
    """An allowed command emits no stderr text."""
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event("rm foo"))
    assert stderr == ""


def test_main_denied_command_exit_code() -> None:
    """A denied command exits 2."""
    code, _ = hook.main(["hook.py", "cmake"], _bash_event("cmake ."))
    assert code == 2


def test_main_denied_command_stderr_names_pattern() -> None:
    """The stderr message names the matched pattern."""
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event("cmake ."))
    assert "cmake" in stderr


def test_main_denied_command_stderr_quotes_command() -> None:
    """The stderr message includes the offending command."""
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event("cmake ."))
    assert "cmake ." in stderr


def test_main_truncates_long_command_in_stderr() -> None:
    """A very long command is truncated to 80 chars in the stderr message."""
    long_cmd = "cmake " + "x" * 200
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event(long_cmd))
    assert "x" * 100 not in stderr


def test_main_no_patterns_exits_zero() -> None:
    """An invocation with no deny patterns auto-allows."""
    code, _ = hook.main(["hook.py"], _bash_event("cmake ."))
    assert code == 0


def test_main_invalid_json_exits_zero() -> None:
    """Invalid JSON on stdin auto-allows (Claude Code retries on hook errors)."""
    code, _ = hook.main(["hook.py", "cmake"], "not json")
    assert code == 0
