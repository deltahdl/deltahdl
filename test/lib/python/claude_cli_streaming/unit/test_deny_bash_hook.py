import io
import json
import runpy
import shlex
import sys

import pytest

from lib.python.claude_cli_streaming import deny_bash_hook as hook


def test_basename_bare_command() -> None:
    assert hook.basename("cmake") == "cmake"


def test_basename_absolute_path() -> None:
    assert hook.basename("/opt/homebrew/bin/cmake") == "cmake"


def test_basename_relative_path() -> None:
    assert hook.basename("./scratchpad/rebuild.sh") == "rebuild.sh"


def test_command_tokens_empty_command() -> None:
    assert not hook.command_tokens("")


def test_command_tokens_whitespace_only_command() -> None:
    assert not hook.command_tokens("   \t  ")


def test_command_tokens_single_command() -> None:
    assert hook.command_tokens("cmake .") == ["cmake"]


def test_command_tokens_and_separator() -> None:
    assert hook.command_tokens("cd /tmp && cmake .") == ["cd", "cmake"]


def test_command_tokens_or_separator() -> None:
    assert hook.command_tokens("make || echo failed") == ["make", "echo"]


def test_command_tokens_semicolon_separator() -> None:
    assert hook.command_tokens("cd /tmp; cmake .") == ["cd", "cmake"]


def test_command_tokens_pipe_separator() -> None:
    assert hook.command_tokens("ls | grep foo") == ["ls", "grep"]


def test_command_tokens_background_separator() -> None:
    assert hook.command_tokens("ninja -C build & wait") == ["ninja", "wait"]


def test_command_tokens_newline_separator() -> None:
    assert hook.command_tokens("cd /tmp\ngit commit") == ["cd", "git"]


def test_command_tokens_carriage_return_separator() -> None:
    assert hook.command_tokens("cd /tmp\r\ngit commit") == ["cd", "git"]


def test_command_tokens_strips_leading_compound_keyword() -> None:
    assert hook.command_tokens("do git add file") == ["git"]


def test_command_tokens_strips_leading_if_keyword() -> None:
    assert hook.command_tokens("if cmake --version") == ["cmake"]


def test_command_tokens_strips_leading_assignment() -> None:
    assert hook.command_tokens("CXX=clang++ cmake .") == ["cmake"]


def test_command_tokens_all_keyword_segment_yields_nothing() -> None:
    assert not hook.command_tokens("do")


def test_command_tokens_skips_empty_segments() -> None:
    assert hook.command_tokens("cmake . ;; make") == ["cmake", "make"]


def test_command_tokens_skips_malformed_segment() -> None:
    assert hook.command_tokens('"unclosed && cmake .') == ["cmake"]


def test_command_tokens_keeps_absolute_path_as_written() -> None:
    assert hook.command_tokens("/opt/homebrew/bin/cmake -S .") == [
        "/opt/homebrew/bin/cmake",
    ]


def test_command_tokens_unwraps_env() -> None:
    assert hook.command_tokens("env NINJA=1 ninja -C build") == ["env", "ninja"]


def test_command_tokens_unwraps_timeout_with_duration() -> None:
    assert hook.command_tokens("timeout 600 make -j8") == ["timeout", "make"]


def test_command_tokens_unwraps_nice_with_flag_argument() -> None:
    assert hook.command_tokens("nice -n 10 ninja") == ["nice", "ninja"]


def test_command_tokens_unwraps_xargs_template() -> None:
    assert hook.command_tokens("xargs -I {} cmake --build {}") == [
        "xargs", "cmake",
    ]


def test_command_tokens_unwraps_shell_dash_c() -> None:
    assert hook.command_tokens('bash -c "cd /tmp && cmake ."') == [
        "bash", "cd", "cmake",
    ]


def test_command_tokens_unwraps_clustered_shell_dash_c() -> None:
    assert hook.command_tokens('bash -lc "make"') == ["bash", "make"]


def test_command_tokens_reports_shell_script_operand() -> None:
    assert hook.command_tokens("bash scratchpad/rebuild_2403.sh") == [
        "bash", "scratchpad/rebuild_2403.sh",
    ]


def test_command_tokens_unwraps_eval_quoted_payload() -> None:
    assert hook.command_tokens('eval "cmake ."') == ["eval", "cmake"]


def test_command_tokens_unwraps_eval_separate_operands() -> None:
    assert hook.command_tokens("eval cmake .") == ["eval", "cmake"]


def test_command_tokens_eval_without_operands() -> None:
    assert hook.command_tokens("eval") == ["eval"]


def test_command_tokens_scans_past_a_hash_on_an_earlier_line() -> None:
    assert hook.command_tokens("ls -la # note\ncmake .") == ["ls", "cmake"]


def test_command_tokens_scans_past_a_hash_inside_a_word() -> None:
    assert hook.command_tokens("echo a#b && cmake .") == ["echo", "cmake"]


def test_command_tokens_recurses_into_command_substitution() -> None:
    assert "cmake" in hook.command_tokens("$(which cmake) -S . -B build")


def test_command_tokens_recurses_into_backticks() -> None:
    assert "make" in hook.command_tokens("echo `make -n`")


def test_command_tokens_skips_redirect_target() -> None:
    assert hook.command_tokens("cmake . > build.log") == ["cmake"]


def test_command_tokens_skips_numbered_redirect_target() -> None:
    assert hook.command_tokens("make 2> errors.log") == ["make"]


def test_command_tokens_shell_with_only_flags() -> None:
    assert hook.command_tokens("bash -x -i") == ["bash"]


def test_command_tokens_skips_empty_fallback_segment() -> None:
    assert hook.command_tokens('"unclosed && && cmake .') == ["cmake"]


def test_command_tokens_unwraps_long_wrapper_chain() -> None:
    assert "cmake" in hook.command_tokens("env " * 12 + "cmake .")


def _nested_shell(depth: int) -> str:
    command = "cmake ."
    for _ in range(depth):
        command = f"bash -c {shlex.quote(command)}"
    return command


def test_command_tokens_unwraps_nested_shells_within_limit() -> None:
    assert "cmake" in hook.command_tokens(_nested_shell(4))


def test_command_tokens_stops_at_reparse_depth_limit() -> None:
    assert "cmake" not in hook.command_tokens(_nested_shell(12))


def _bash_event(command: str) -> str:
    return json.dumps({"tool_name": "Bash", "tool_input": {"command": command}})


def test_extract_bash_command_valid_event() -> None:
    assert hook.extract_bash_command(_bash_event("cmake .")) == "cmake ."


def test_extract_bash_command_invalid_json() -> None:
    assert hook.extract_bash_command("not json") is None


def test_extract_bash_command_non_dict_json() -> None:
    assert hook.extract_bash_command("[]") is None


def test_extract_bash_command_non_bash_tool() -> None:
    payload = json.dumps({"tool_name": "Read", "tool_input": {"file_path": "x"}})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_missing_tool_input() -> None:
    assert hook.extract_bash_command(json.dumps({"tool_name": "Bash"})) is None


def test_extract_bash_command_non_dict_tool_input() -> None:
    payload = json.dumps({"tool_name": "Bash", "tool_input": "cmake ."})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_missing_command() -> None:
    payload = json.dumps({"tool_name": "Bash", "tool_input": {}})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_non_string_command() -> None:
    payload = json.dumps({"tool_name": "Bash", "tool_input": {"command": 42}})
    assert hook.extract_bash_command(payload) is None


def test_extract_bash_command_empty_command() -> None:
    assert hook.extract_bash_command(_bash_event("")) is None


def test_match_deny_pattern_no_patterns() -> None:
    assert hook.match_deny_pattern(_bash_event("cmake ."), []) is None


def test_match_deny_pattern_direct_match() -> None:
    assert hook.match_deny_pattern(
        _bash_event("cmake ."), ["cmake"],
    ) == ("cmake", "cmake .")


def test_match_deny_pattern_chained_command() -> None:
    assert hook.match_deny_pattern(
        _bash_event("cd /tmp && cmake ."), ["cmake"],
    ) == ("cmake", "cd /tmp && cmake .")


def test_match_deny_pattern_newline_chained_command() -> None:
    event = _bash_event("cd /repo\ngit commit -q -m x")
    assert hook.match_deny_pattern(event, ["git"]) == (
        "git", "cd /repo\ngit commit -q -m x",
    )


def test_match_deny_pattern_absolute_path_invocation() -> None:
    event = _bash_event("/opt/homebrew/bin/cmake -S . -B build")
    assert hook.match_deny_pattern(event, ["cmake"]) is not None


def test_match_deny_pattern_env_wrapped_invocation() -> None:
    event = _bash_event("env NINJA_STATUS=x ninja -C build")
    assert hook.match_deny_pattern(event, ["ninja"]) is not None


def test_match_deny_pattern_shell_dash_c_invocation() -> None:
    event = _bash_event('bash -c "cd /repo && make -j8"')
    assert hook.match_deny_pattern(event, ["make"]) is not None


def test_match_deny_pattern_eval_invocation() -> None:
    event = _bash_event('eval "cmake -S . -B build"')
    assert hook.match_deny_pattern(event, ["cmake"]) is not None


def test_match_deny_pattern_command_after_a_comment_line() -> None:
    event = _bash_event("# configure the tree\ncmake -S . -B build")
    assert hook.match_deny_pattern(event, ["cmake"]) is not None


def test_match_deny_pattern_glob_over_basename() -> None:
    event = _bash_event("/usr/bin/clang++ -std=c++23 -c x.cpp")
    assert hook.match_deny_pattern(event, ["clang*"]) == (
        "clang*", "/usr/bin/clang++ -std=c++23 -c x.cpp",
    )


def test_match_deny_pattern_glob_over_shell_script() -> None:
    event = _bash_event("bash scratchpad/rebuild_2403.sh")
    assert hook.match_deny_pattern(event, ["*.sh"]) is not None


def test_match_deny_pattern_glob_over_build_tree_path() -> None:
    event = _bash_event("build-b2debug/bin/test_parser --gtest_filter=X")
    assert hook.match_deny_pattern(event, ["build*/*"]) is not None


def test_match_deny_pattern_ignores_denied_name_as_argument() -> None:
    event = _bash_event("grep -rn cmake test/CMakeLists.txt")
    assert hook.match_deny_pattern(event, ["cmake"]) is None


def test_match_deny_pattern_no_match() -> None:
    assert hook.match_deny_pattern(_bash_event("rm foo"), ["cmake"]) is None


def test_match_deny_pattern_non_bash_event() -> None:
    payload = json.dumps({"tool_name": "Read", "tool_input": {"file_path": "x"}})
    assert hook.match_deny_pattern(payload, ["cmake"]) is None


def test_main_allowed_command_exit_code() -> None:
    code, _ = hook.main(["hook.py", "cmake"], _bash_event("rm foo"))
    assert code == 0


def test_main_allowed_command_empty_stderr() -> None:
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event("rm foo"))
    assert stderr == ""


def test_main_denied_command_exit_code() -> None:
    code, _ = hook.main(["hook.py", "cmake"], _bash_event("cmake ."))
    assert code == 2


def test_main_denied_command_stderr_names_pattern() -> None:
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event("cmake ."))
    assert "cmake" in stderr


def test_main_denied_command_stderr_quotes_command() -> None:
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event("cmake ."))
    assert "cmake ." in stderr


def test_main_truncates_long_command_in_stderr() -> None:
    long_cmd = "cmake " + "x" * 200
    _, stderr = hook.main(["hook.py", "cmake"], _bash_event(long_cmd))
    assert "x" * 100 not in stderr


def test_main_denied_after_newline_exit_code() -> None:
    code, _ = hook.main(["hook.py", "git"], _bash_event("cd /repo\ngit commit"))
    assert code == 2


def test_main_no_patterns_exits_zero() -> None:
    code, _ = hook.main(["hook.py"], _bash_event("cmake ."))
    assert code == 0


def test_main_invalid_json_exits_zero() -> None:
    code, _ = hook.main(["hook.py", "cmake"], "not json")
    assert code == 0


def _exit_code_run_as_a_hook(
    monkeypatch: pytest.MonkeyPatch, command: str,
) -> int | str | None:
    monkeypatch.setattr(sys, "argv", ["deny_bash_hook.py", "cmake"])
    monkeypatch.setattr(sys, "stdin", io.StringIO(_bash_event(command)))
    monkeypatch.delitem(sys.modules, hook.__name__)
    with pytest.raises(SystemExit) as exit_info:
        runpy.run_module(hook.__name__, run_name="__main__")
    return exit_info.value.code


def test_run_as_a_hook_exits_two_on_a_denied_command(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    assert _exit_code_run_as_a_hook(monkeypatch, "cmake .") == 2


def test_run_as_a_hook_prints_the_block_on_stderr(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    _exit_code_run_as_a_hook(monkeypatch, "cmake .")
    assert "Blocked: cmake in cmake ." in capsys.readouterr().err


def test_run_as_a_hook_exits_zero_on_an_allowed_command(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    assert _exit_code_run_as_a_hook(monkeypatch, "rm foo") == 0


def test_run_as_a_hook_prints_nothing_on_an_allowed_command(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str],
) -> None:
    _exit_code_run_as_a_hook(monkeypatch, "rm foo")
    assert capsys.readouterr().err == ""
