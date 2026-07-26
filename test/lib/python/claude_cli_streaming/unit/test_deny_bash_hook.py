"""Unit tests for lib.python.claude_cli_streaming.deny_bash_hook."""

import json
import shlex

from lib.python.claude_cli_streaming import deny_bash_hook as hook


# --- basename ---------------------------------------------------------------


def test_basename_bare_command() -> None:
    """A bare command name is its own basename."""
    assert hook.basename("cmake") == "cmake"


def test_basename_absolute_path() -> None:
    """An absolute path reduces to its last component."""
    assert hook.basename("/opt/homebrew/bin/cmake") == "cmake"


def test_basename_relative_path() -> None:
    """A relative path reduces to its last component."""
    assert hook.basename("./scratchpad/rebuild.sh") == "rebuild.sh"


# --- command_tokens ---------------------------------------------------------


def test_command_tokens_empty_command() -> None:
    """An empty command returns an empty list."""
    assert not hook.command_tokens("")


def test_command_tokens_whitespace_only_command() -> None:
    """A whitespace-only command returns an empty list."""
    assert not hook.command_tokens("   \t  ")


def test_command_tokens_single_command() -> None:
    """A single command returns its first token in a single-element list."""
    assert hook.command_tokens("cmake .") == ["cmake"]


def test_command_tokens_and_separator() -> None:
    """`&&` splits subcommands and each command position is collected."""
    assert hook.command_tokens("cd /tmp && cmake .") == ["cd", "cmake"]


def test_command_tokens_or_separator() -> None:
    """`||` splits subcommands."""
    assert hook.command_tokens("make || echo failed") == ["make", "echo"]


def test_command_tokens_semicolon_separator() -> None:
    """`;` splits subcommands."""
    assert hook.command_tokens("cd /tmp; cmake .") == ["cd", "cmake"]


def test_command_tokens_pipe_separator() -> None:
    """A single `|` splits a pipeline."""
    assert hook.command_tokens("ls | grep foo") == ["ls", "grep"]


def test_command_tokens_background_separator() -> None:
    """A trailing `&` splits a backgrounded subcommand."""
    assert hook.command_tokens("ninja -C build & wait") == ["ninja", "wait"]


def test_command_tokens_newline_separator() -> None:
    """A newline splits subcommands like an operator does."""
    assert hook.command_tokens("cd /tmp\ngit commit") == ["cd", "git"]


def test_command_tokens_carriage_return_separator() -> None:
    """A CRLF line ending splits subcommands without a stray token."""
    assert hook.command_tokens("cd /tmp\r\ngit commit") == ["cd", "git"]


def test_command_tokens_strips_leading_compound_keyword() -> None:
    """A leading compound-command keyword is skipped to reach the command."""
    assert hook.command_tokens("do git add file") == ["git"]


def test_command_tokens_strips_leading_if_keyword() -> None:
    """A leading `if` is skipped to reach the command it tests."""
    assert hook.command_tokens("if cmake --version") == ["cmake"]


def test_command_tokens_strips_leading_assignment() -> None:
    """A leading environment assignment is skipped to reach the command."""
    assert hook.command_tokens("CXX=clang++ cmake .") == ["cmake"]


def test_command_tokens_all_keyword_segment_yields_nothing() -> None:
    """A segment that is only compound-command keywords contributes nothing."""
    assert not hook.command_tokens("do")


def test_command_tokens_skips_empty_segments() -> None:
    """Empty subcommands between operators are skipped."""
    assert hook.command_tokens("cmake . ;; make") == ["cmake", "make"]


def test_command_tokens_skips_malformed_segment() -> None:
    """A malformed segment is skipped without dropping later ones."""
    assert hook.command_tokens('"unclosed && cmake .') == ["cmake"]


def test_command_tokens_keeps_absolute_path_as_written() -> None:
    """An absolute-path invocation is reported as the token it was written as."""
    assert hook.command_tokens("/opt/homebrew/bin/cmake -S .") == [
        "/opt/homebrew/bin/cmake",
    ]


def test_command_tokens_unwraps_env() -> None:
    """`env` contributes the command it runs as a further command position."""
    assert hook.command_tokens("env NINJA=1 ninja -C build") == ["env", "ninja"]


def test_command_tokens_unwraps_timeout_with_duration() -> None:
    """A wrapper's numeric operand is skipped to reach the wrapped command."""
    assert hook.command_tokens("timeout 600 make -j8") == ["timeout", "make"]


def test_command_tokens_unwraps_nice_with_flag_argument() -> None:
    """A wrapper's flag and its value are skipped to reach the command."""
    assert hook.command_tokens("nice -n 10 ninja") == ["nice", "ninja"]


def test_command_tokens_unwraps_xargs_template() -> None:
    """An `xargs -I {}` template does not hide the command it runs."""
    assert hook.command_tokens("xargs -I {} cmake --build {}") == [
        "xargs", "cmake",
    ]


def test_command_tokens_unwraps_shell_dash_c() -> None:
    """A `sh -c` payload is re-parsed as a command string."""
    assert hook.command_tokens('bash -c "cd /tmp && cmake ."') == [
        "bash", "cd", "cmake",
    ]


def test_command_tokens_unwraps_clustered_shell_dash_c() -> None:
    """A clustered `-lc` payload is re-parsed like a plain `-c` one."""
    assert hook.command_tokens('bash -lc "make"') == ["bash", "make"]


def test_command_tokens_reports_shell_script_operand() -> None:
    """A script path run through a shell is itself a command position."""
    assert hook.command_tokens("bash scratchpad/rebuild_2403.sh") == [
        "bash", "scratchpad/rebuild_2403.sh",
    ]


def test_command_tokens_unwraps_eval_quoted_payload() -> None:
    """An `eval` payload given as one quoted string is re-parsed."""
    assert hook.command_tokens('eval "cmake ."') == ["eval", "cmake"]


def test_command_tokens_unwraps_eval_separate_operands() -> None:
    """`eval`'s operands are rejoined before being re-parsed."""
    assert hook.command_tokens("eval cmake .") == ["eval", "cmake"]


def test_command_tokens_eval_without_operands() -> None:
    """A bare `eval` re-parses an empty string and contributes nothing more."""
    assert hook.command_tokens("eval") == ["eval"]


def test_command_tokens_scans_past_a_hash_on_an_earlier_line() -> None:
    """A `#` does not end the scan, so a later line is still reached."""
    assert hook.command_tokens("ls -la # note\ncmake .") == ["ls", "cmake"]


def test_command_tokens_scans_past_a_hash_inside_a_word() -> None:
    """A `#` inside a word does not end the scan of the same line."""
    assert hook.command_tokens("echo a#b && cmake .") == ["echo", "cmake"]


def test_command_tokens_recurses_into_command_substitution() -> None:
    """A `$(...)` body is scanned for command positions."""
    assert "cmake" in hook.command_tokens("$(which cmake) -S . -B build")


def test_command_tokens_recurses_into_backticks() -> None:
    """A backtick substitution body is scanned for command positions."""
    assert "make" in hook.command_tokens("echo `make -n`")


def test_command_tokens_skips_redirect_target() -> None:
    """A redirection target is a file, not a command position."""
    assert hook.command_tokens("cmake . > build.log") == ["cmake"]


def test_command_tokens_skips_numbered_redirect_target() -> None:
    """A numbered redirection target is skipped too."""
    assert hook.command_tokens("make 2> errors.log") == ["make"]


def test_command_tokens_shell_with_only_flags() -> None:
    """A shell invoked with flags but no command or script yields no operand."""
    assert hook.command_tokens("bash -x -i") == ["bash"]


def test_command_tokens_skips_empty_fallback_segment() -> None:
    """An empty segment on the malformed-command fallback path is skipped."""
    assert hook.command_tokens('"unclosed && && cmake .') == ["cmake"]


def test_command_tokens_unwraps_long_wrapper_chain() -> None:
    """A long wrapper chain still reaches the command it wraps."""
    assert "cmake" in hook.command_tokens("env " * 12 + "cmake .")


def _nested_shell(depth: int) -> str:
    """Return ``cmake .`` wrapped in *depth* levels of ``bash -c``."""
    command = "cmake ."
    for _ in range(depth):
        command = f"bash -c {shlex.quote(command)}"
    return command


def test_command_tokens_unwraps_nested_shells_within_limit() -> None:
    """A few levels of nested `bash -c` still reach the wrapped command."""
    assert "cmake" in hook.command_tokens(_nested_shell(4))


def test_command_tokens_stops_at_reparse_depth_limit() -> None:
    """Re-parsing a payload as a command is depth-bounded."""
    assert "cmake" not in hook.command_tokens(_nested_shell(12))


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


def test_match_deny_pattern_newline_chained_command() -> None:
    """A denied token reached after a newline is also matched."""
    event = _bash_event("cd /repo\ngit commit -q -m x")
    assert hook.match_deny_pattern(event, ["git"]) == (
        "git", "cd /repo\ngit commit -q -m x",
    )


def test_match_deny_pattern_absolute_path_invocation() -> None:
    """A bare pattern blocks the same tool invoked by absolute path."""
    event = _bash_event("/opt/homebrew/bin/cmake -S . -B build")
    assert hook.match_deny_pattern(event, ["cmake"]) is not None


def test_match_deny_pattern_env_wrapped_invocation() -> None:
    """A bare pattern blocks the same tool wrapped in `env`."""
    event = _bash_event("env NINJA_STATUS=x ninja -C build")
    assert hook.match_deny_pattern(event, ["ninja"]) is not None


def test_match_deny_pattern_shell_dash_c_invocation() -> None:
    """A bare pattern blocks the same tool run through `bash -c`."""
    event = _bash_event('bash -c "cd /repo && make -j8"')
    assert hook.match_deny_pattern(event, ["make"]) is not None


def test_match_deny_pattern_eval_invocation() -> None:
    """A bare pattern blocks the same tool handed to `eval` as text."""
    event = _bash_event('eval "cmake -S . -B build"')
    assert hook.match_deny_pattern(event, ["cmake"]) is not None


def test_match_deny_pattern_command_after_a_comment_line() -> None:
    """A `#` earlier in the command does not hide a later invocation."""
    event = _bash_event("# configure the tree\ncmake -S . -B build")
    assert hook.match_deny_pattern(event, ["cmake"]) is not None


def test_match_deny_pattern_glob_over_basename() -> None:
    """A glob pattern matches the basename of a path invocation."""
    event = _bash_event("/usr/bin/clang++ -std=c++23 -c x.cpp")
    assert hook.match_deny_pattern(event, ["clang*"]) == (
        "clang*", "/usr/bin/clang++ -std=c++23 -c x.cpp",
    )


def test_match_deny_pattern_glob_over_shell_script() -> None:
    """A `*.sh` glob blocks a build script run through a shell."""
    event = _bash_event("bash scratchpad/rebuild_2403.sh")
    assert hook.match_deny_pattern(event, ["*.sh"]) is not None


def test_match_deny_pattern_glob_over_build_tree_path() -> None:
    """A `build*/*` glob blocks executing an artefact from a build tree."""
    event = _bash_event("build-b2debug/bin/test_parser --gtest_filter=X")
    assert hook.match_deny_pattern(event, ["build*/*"]) is not None


def test_match_deny_pattern_ignores_denied_name_as_argument() -> None:
    """A denied name appearing only as an argument does not block."""
    event = _bash_event("grep -rn cmake test/CMakeLists.txt")
    assert hook.match_deny_pattern(event, ["cmake"]) is None


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


def test_main_denied_after_newline_exit_code() -> None:
    """A denied command on a line after `cd` still exits 2."""
    code, _ = hook.main(["hook.py", "git"], _bash_event("cd /repo\ngit commit"))
    assert code == 2


def test_main_no_patterns_exits_zero() -> None:
    """An invocation with no deny patterns auto-allows."""
    code, _ = hook.main(["hook.py"], _bash_event("cmake ."))
    assert code == 0


def test_main_invalid_json_exits_zero() -> None:
    """Invalid JSON on stdin auto-allows (Claude Code retries on hook errors)."""
    code, _ = hook.main(["hook.py", "cmake"], "not json")
    assert code == 0
