"""Unit tests for satisfy_subclause.oracles."""

from unittest.mock import patch

import pytest

from satisfy_subclause.oracles import (
    DISALLOWED_TOOLS,
    build_dependency_prompt,
    build_env,
    compute_subclause_dependencies,
    parse_dependencies,
    run_oracle_call,
)


# --- DISALLOWED_TOOLS -------------------------------------------------------


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


def test_disallowed_tools_blocks_pdftotext() -> None:
    """The disallowed-tools list blocks Bash(pdftotext *)."""
    assert "pdftotext" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pdfgrep() -> None:
    """The disallowed-tools list blocks Bash(pdfgrep *)."""
    assert "pdfgrep" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pdftohtml() -> None:
    """The disallowed-tools list blocks Bash(pdftohtml *)."""
    assert "pdftohtml" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pdftoppm() -> None:
    """The disallowed-tools list blocks Bash(pdftoppm *)."""
    assert "pdftoppm" in DISALLOWED_TOOLS


def test_disallowed_tools_blocks_mutool() -> None:
    """The disallowed-tools list blocks Bash(mutool *)."""
    assert "mutool" in DISALLOWED_TOOLS


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


# --- run_oracle_call --------------------------------------------------------


def _patched_streaming(result_text="DONE"):
    """Patch run_claude_streaming with a fixed return string."""
    return patch(
        "satisfy_subclause.oracles.run_claude_streaming",
        return_value=result_text,
    )


def test_run_oracle_call_returns_result_text() -> None:
    """Returns the .result string forwarded by the streaming runner."""
    with _patched_streaming("DONE"):
        assert run_oracle_call("prompt", model="opus") == "DONE"


def test_run_oracle_call_passes_prompt() -> None:
    """Forwards the prompt to run_claude_streaming."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("hello prompt", model="opus")
    assert mock_stream.call_args[0][1] == "hello prompt"


def test_run_oracle_call_passes_model_to_cli() -> None:
    """Passes the model argument to the Claude CLI."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="haiku")
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_oracle_call_uses_stream_json() -> None:
    """Requests --output-format stream-json so events stream live."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_run_oracle_call_uses_verbose() -> None:
    """Invokes the Claude CLI with --verbose (required for stream-json)."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--verbose" in mock_stream.call_args[0][0]


def test_run_oracle_call_passes_disallowed_tools() -> None:
    """Passes --disallowedTools to the Claude CLI."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--disallowedTools" in mock_stream.call_args[0][0]


def test_run_oracle_call_uses_dangerously_skip_permissions() -> None:
    """Invokes the Claude CLI with --dangerously-skip-permissions."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--dangerously-skip-permissions" in mock_stream.call_args[0][0]


def test_run_oracle_call_does_not_continue_session() -> None:
    """The dependency oracle never opens a continued session."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--continue" not in mock_stream.call_args[0][0]


def test_run_oracle_call_passes_clean_env() -> None:
    """Passes a CLAUDECODE-scrubbed env to the streaming runner."""
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        with _patched_streaming() as mock_stream:
            run_oracle_call("prompt", model="opus")
    assert "CLAUDECODE" not in mock_stream.call_args[1]["env"]


# --- build_dependency_prompt ------------------------------------------------


def test_build_dependency_prompt_mentions_subclause() -> None:
    """Prompt mentions the target subclause."""
    assert "§33.4.1.5" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_mentions_read_only() -> None:
    """Prompt explicitly states the oracle is read-only."""
    assert "READ-ONLY" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_mentions_lrm() -> None:
    """Prompt embeds the LRM path."""
    assert "~/LRM.pdf" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_describes_required_relation() -> None:
    """Prompt explains the dependency relation as REQUIRED-before."""
    assert "REQUIRED" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_describes_parent_rollup() -> None:
    """Prompt explains the parent-rolls-up-over-children rule."""
    assert "child" in build_dependency_prompt("33.4", "~/LRM.pdf")


def test_build_dependency_prompt_requests_json_array() -> None:
    """Prompt instructs the oracle to output a single JSON array."""
    assert "JSON array" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_says_empty_if_none() -> None:
    """Prompt instructs an empty array when no dependencies exist."""
    assert "[]" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


# --- parse_dependencies -----------------------------------------------------


def test_parse_dependencies_empty() -> None:
    """An empty array parses to an empty list."""
    assert not parse_dependencies("[]")


def test_parse_dependencies_single_entry() -> None:
    """A single subclause string parses through verbatim."""
    assert parse_dependencies('["33.6.1"]') == ["33.6.1"]


def test_parse_dependencies_preserves_order() -> None:
    """Dependencies are returned in the order the oracle listed them."""
    text = '["33.6.1", "33.4.1.5", "33.4.1.6"]'
    assert parse_dependencies(text) == [
        "33.6.1", "33.4.1.5", "33.4.1.6",
    ]


def test_parse_dependencies_handles_fenced_array() -> None:
    """A fenced JSON array oracle response parses."""
    text = '```json\n["33.6.1"]\n```'
    assert parse_dependencies(text) == ["33.6.1"]


def test_parse_dependencies_handles_unmarked_fence() -> None:
    """A bare ``` fence (no language) parses."""
    text = '```\n["33.6.1"]\n```'
    assert parse_dependencies(text) == ["33.6.1"]


def test_parse_dependencies_handles_text_before_array() -> None:
    """A bare array surrounded by prose parses."""
    text = 'preamble ["33.6.1"] trailer'
    assert parse_dependencies(text) == ["33.6.1"]


def test_parse_dependencies_accepts_annex() -> None:
    """An annex-letter dependency entry is accepted."""
    assert parse_dependencies('["A.7"]') == ["A.7"]


def test_parse_dependencies_rejects_non_string_entry() -> None:
    """A non-string entry in the array is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('[42]')


def test_parse_dependencies_rejects_garbage_entry() -> None:
    """An entry that is not a valid clause identifier is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('["not-a-clause"]')


def test_parse_dependencies_rejects_lowercase_letter() -> None:
    """A lowercase letter clause is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('["a.7"]')


def test_parse_dependencies_rejects_text_without_array() -> None:
    """Output without a JSON array raises ValueError."""
    with pytest.raises(ValueError):
        parse_dependencies("no array here")


# --- compute_subclause_dependencies -----------------------------------------


def _patched_oracle(result_text):
    """Patch run_oracle_call with a fixed return string."""
    return patch(
        "satisfy_subclause.oracles.run_oracle_call",
        return_value=result_text,
    )


def test_compute_subclause_dependencies_returns_list() -> None:
    """compute_subclause_dependencies returns the parsed list."""
    with _patched_oracle('["33.6.1"]'):
        deps = compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus",
        )
    assert deps == ["33.6.1"]


def test_compute_subclause_dependencies_passes_model() -> None:
    """compute_subclause_dependencies forwards the model arg."""
    with _patched_oracle("[]") as mock_run:
        compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="haiku",
        )
    assert mock_run.call_args[1]["model"] == "haiku"


def test_compute_subclause_dependencies_logs_banner_to_stderr(capsys) -> None:
    """compute_subclause_dependencies prints a dependency-oracle banner."""
    with _patched_oracle("[]"):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "Dependency" in capsys.readouterr().err


def test_compute_subclause_dependencies_logs_subclause_to_stderr(
    capsys,
) -> None:
    """compute_subclause_dependencies includes the subclause in its banner."""
    with _patched_oracle("[]"):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "§33.4" in capsys.readouterr().err
