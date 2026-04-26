"""Tests for lib.python.satisfy.oracle (shared Claude-CLI plumbing)."""

import json
from unittest.mock import patch

import pytest

from lib.python.satisfy.oracle import (
    DISALLOWED_TOOLS,
    build_env,
    build_oracle_args,
    extract_json_literal,
    run_oracle_call,
)
from lib.python.test_fixtures.satisfy import stub_completed


# --- DISALLOWED_TOOLS --------------------------------------------------------


def test_disallowed_tools_blocks_write() -> None:
    """The disallowed-tools list blocks the Write tool."""
    assert "Write" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_edit() -> None:
    """The disallowed-tools list blocks the Edit tool."""
    assert "Edit" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_multiedit() -> None:
    """The disallowed-tools list blocks MultiEdit."""
    assert "MultiEdit" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_notebookedit() -> None:
    """The disallowed-tools list blocks NotebookEdit."""
    assert "NotebookEdit" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_git_commit() -> None:
    """The disallowed-tools list blocks Bash(git commit *)."""
    assert "git commit" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_rm() -> None:
    """The disallowed-tools list blocks Bash(rm *)."""
    assert "rm *" in DISALLOWED_TOOLS


# --- build_env --------------------------------------------------------------


def test_build_env_drops_claudecode() -> None:
    """build_env removes the CLAUDECODE variable when set."""
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        env = build_env()
    assert "CLAUDECODE" not in env


def test_build_env_when_claudecode_unset() -> None:
    """build_env succeeds when CLAUDECODE is not set."""
    with patch.dict("os.environ", {}, clear=True):
        env = build_env()
    assert "CLAUDECODE" not in env


def test_build_env_preserves_other_vars() -> None:
    """build_env preserves unrelated environment variables."""
    with patch.dict("os.environ", {"ORACLE_VAR": "value"}, clear=False):
        env = build_env()
    assert env.get("ORACLE_VAR") == "value"


# --- extract_json_literal ---------------------------------------------------


def test_extract_json_literal_bare_object() -> None:
    """A bare JSON object is extracted verbatim."""
    assert extract_json_literal('{"a": 1}') == '{"a": 1}'


def test_extract_json_literal_bare_array() -> None:
    """A bare JSON array is extracted verbatim."""
    assert extract_json_literal('["a", "b"]') == '["a", "b"]'


def test_extract_json_literal_object_with_surrounding_text() -> None:
    """A JSON object surrounded by text is extracted."""
    assert extract_json_literal('preamble {"x": 1} trailer') == '{"x": 1}'


def test_extract_json_literal_array_with_surrounding_text() -> None:
    """A JSON array surrounded by text is extracted."""
    assert extract_json_literal('preamble ["x"] trailer') == '["x"]'


def test_extract_json_literal_fenced_object() -> None:
    """A JSON object inside a ```json``` fence is extracted."""
    text = '```json\n{"a": 1}\n```'
    assert extract_json_literal(text) == '{"a": 1}'


def test_extract_json_literal_fenced_array() -> None:
    """A JSON array inside a ```json``` fence is extracted."""
    text = '```json\n["a", "b"]\n```'
    assert extract_json_literal(text) == '["a", "b"]'


def test_extract_json_literal_fenced_no_lang_object() -> None:
    """A JSON object inside an unmarked code fence is extracted."""
    text = '```\n{"a": 1}\n```'
    assert extract_json_literal(text) == '{"a": 1}'


def test_extract_json_literal_fenced_no_lang_array() -> None:
    """A JSON array inside an unmarked code fence is extracted."""
    text = '```\n["a"]\n```'
    assert extract_json_literal(text) == '["a"]'


def test_extract_json_literal_prefers_object_over_array() -> None:
    """When both shapes appear, the object wins (oracle outputs JSON)."""
    text = '{"x": 1} ["y"]'
    assert extract_json_literal(text) == '{"x": 1}'


def test_extract_json_literal_raises_when_missing() -> None:
    """Text without any JSON literal raises ValueError."""
    with pytest.raises(ValueError):
        extract_json_literal("no json here")


# --- build_oracle_args ------------------------------------------------------


def test_build_oracle_args_returns_subclause(tmp_path) -> None:
    """build_oracle_args returns the parsed subclause."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    args = build_oracle_args(
        "test description",
        ["--lrm", str(lrm), "--subclause", "33.4.1.5"],
    )
    assert args.subclause == "33.4.1.5"


def test_build_oracle_args_returns_default_model(tmp_path) -> None:
    """build_oracle_args returns the default 'opus' model when omitted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    args = build_oracle_args(
        "test description",
        ["--lrm", str(lrm), "--subclause", "33.4.1.5"],
    )
    assert args.model == "opus"


def test_build_oracle_args_returns_overridden_model(tmp_path) -> None:
    """build_oracle_args returns an explicitly-passed model override."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    args = build_oracle_args(
        "test description",
        ["--lrm", str(lrm), "--subclause", "4.1", "--model", "haiku"],
    )
    assert args.model == "haiku"


def test_build_oracle_args_rejects_bad_subclause(tmp_path) -> None:
    """build_oracle_args exits when --subclause is invalid."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    with pytest.raises(SystemExit):
        build_oracle_args(
            "test description",
            ["--lrm", str(lrm), "--subclause", "garbage"],
        )


def test_build_oracle_args_rejects_missing_lrm(tmp_path) -> None:
    """build_oracle_args exits when --lrm points at a non-existent file."""
    with pytest.raises(SystemExit):
        build_oracle_args(
            "test description",
            ["--lrm", str(tmp_path / "no.pdf"), "--subclause", "4.1"],
        )


# --- run_oracle_call --------------------------------------------------------


def _patched(stdout, *, returncode=0, stderr=""):
    """Patch subprocess.run with a stubbed CompletedProcess."""
    return patch(
        "lib.python.satisfy.oracle.subprocess.run",
        return_value=stub_completed(
            stdout=stdout, returncode=returncode, stderr=stderr,
        ),
    )


def _ok_stdout(result_text="DONE"):
    """Build a successful Claude --output-format json stdout payload."""
    return json.dumps({"result": result_text})


def test_run_oracle_call_returns_result_text() -> None:
    """Returns the .result string from the Claude CLI payload."""
    with _patched(_ok_stdout("DONE")):
        text = run_oracle_call("prompt", model="opus")
    assert text == "DONE"


def test_run_oracle_call_passes_prompt_to_stdin() -> None:
    """Passes the prompt to subprocess.run as stdin."""
    with _patched(_ok_stdout()) as mock_run:
        run_oracle_call("hello prompt", model="opus")
    assert mock_run.call_args[1]["input"] == "hello prompt"


def test_run_oracle_call_passes_model_to_cli() -> None:
    """Passes the model argument to the Claude CLI."""
    with _patched(_ok_stdout()) as mock_run:
        run_oracle_call("prompt", model="haiku")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_oracle_call_uses_json_output_format() -> None:
    """Requests --output-format json from the Claude CLI."""
    with _patched(_ok_stdout()) as mock_run:
        run_oracle_call("prompt", model="opus")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--output-format") + 1] == "json"


def test_run_oracle_call_passes_disallowed_tools() -> None:
    """Passes --disallowedTools to the Claude CLI."""
    with _patched(_ok_stdout()) as mock_run:
        run_oracle_call("prompt", model="opus")
    assert "--disallowedTools" in mock_run.call_args[0][0]


def test_run_oracle_call_uses_dangerously_skip_permissions() -> None:
    """Invokes the Claude CLI with --dangerously-skip-permissions."""
    with _patched(_ok_stdout()) as mock_run:
        run_oracle_call("prompt", model="opus")
    assert "--dangerously-skip-permissions" in mock_run.call_args[0][0]


def test_run_oracle_call_passes_clean_env() -> None:
    """Passes a CLAUDECODE-scrubbed env to subprocess.run."""
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        with _patched(_ok_stdout()) as mock_run:
            run_oracle_call("prompt", model="opus")
    assert "CLAUDECODE" not in mock_run.call_args[1]["env"]


def test_run_oracle_call_exits_on_nonzero() -> None:
    """A non-zero exit code is loud-fatal."""
    with _patched("", returncode=1, stderr="boom"):
        with pytest.raises(SystemExit):
            run_oracle_call("prompt", model="opus")


def test_run_oracle_call_dumps_stderr_on_nonzero(capsys) -> None:
    """Non-zero exit dumps stderr to the terminal."""
    with _patched("", returncode=1, stderr="UNIQUE_ORACLE_STDERR"):
        try:
            run_oracle_call("prompt", model="opus")
        except SystemExit:
            pass
    assert "UNIQUE_ORACLE_STDERR" in capsys.readouterr().err


def test_run_oracle_call_exits_on_non_json_stdout() -> None:
    """Non-JSON stdout from the Claude CLI is loud-fatal."""
    with _patched("not json"):
        with pytest.raises(SystemExit):
            run_oracle_call("prompt", model="opus")


def test_run_oracle_call_dumps_non_json_stdout(capsys) -> None:
    """Non-JSON stdout is echoed to stderr."""
    with _patched("ORACLE_BAD_JSON"):
        try:
            run_oracle_call("prompt", model="opus")
        except SystemExit:
            pass
    assert "ORACLE_BAD_JSON" in capsys.readouterr().err


def test_run_oracle_call_exits_when_result_missing() -> None:
    """Claude payload without a .result field is loud-fatal."""
    with _patched(json.dumps({"other": "value"})):
        with pytest.raises(SystemExit):
            run_oracle_call("prompt", model="opus")


def test_run_oracle_call_exits_when_result_empty() -> None:
    """Claude payload with empty .result is loud-fatal."""
    with _patched(json.dumps({"result": ""})):
        with pytest.raises(SystemExit):
            run_oracle_call("prompt", model="opus")


def test_run_oracle_call_exits_when_result_non_string() -> None:
    """Claude payload with non-string .result is loud-fatal."""
    with _patched(json.dumps({"result": 42})):
        with pytest.raises(SystemExit):
            run_oracle_call("prompt", model="opus")
