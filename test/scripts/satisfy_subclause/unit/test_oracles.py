"""Unit tests for satisfy_subclause.oracles."""

from typing import Any
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


def _patched_streaming(result_text: str = "DONE") -> Any:
    """Patch run_claude_streaming with a fixed return string."""
    return patch(
        "satisfy_subclause.oracles.run_claude_streaming_with_retry",
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
    assert "read-only" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_mentions_lrm() -> None:
    """Prompt embeds the LRM path."""
    assert "~/LRM.pdf" in build_dependency_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_dependency_prompt_grounds_in_normative_rule() -> None:
    """Prompt anchors a dependency on a normative rule §X states."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "normative rule" in prompt


def test_build_dependency_prompt_anchors_dep_on_machinery_prereq() -> None:
    """Prompt anchors a dependency on §Y's machinery being a prerequisite."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "machinery" in prompt


def test_build_dependency_prompt_invites_quotable_evidence() -> None:
    """Prompt asks for a quotable §X sentence as the dep's grounding."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "quote" in prompt


def test_build_dependency_prompt_drops_term_use_criterion() -> None:
    """Prompt no longer treats vocabulary mentions as a dep criterion."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "term, function, or syntactic construct" not in prompt


def test_build_dependency_prompt_orders_foundations_first() -> None:
    """Prompt instructs ordering by foundation-then-builds-on."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "foundations-first" in prompt


def test_build_dependency_prompt_avoids_required_emphasis() -> None:
    """Prompt no longer leans on the 'REQUIRED' framing."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "REQUIRED" not in prompt


def test_build_dependency_prompt_drops_parent_rollup_rule() -> None:
    """Prompt no longer reframes parent satisfaction as a child dependency."""
    prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "rolls up" not in prompt


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


def test_parse_dependencies_picks_last_array_when_prose_has_brackets() -> None:
    """Prose containing a bracketed example doesn't swallow the real array."""
    text = (
        "Reasoning: §3.9 says [example with typedef struct, function].\n\n"
        "It defers all syntax to Clause 26.\n\n"
        "[]"
    )
    assert not parse_dependencies(text)


def test_parse_dependencies_picks_last_nonempty_array_when_prose_has_brackets() -> None:
    """A non-empty final array is picked over earlier bracketed prose."""
    text = (
        "Earlier prose [unrelated bracketed text] more prose.\n\n"
        '["33.6.1", "33.4.1.5"]'
    )
    assert parse_dependencies(text) == ["33.6.1", "33.4.1.5"]


# --- compute_subclause_dependencies -----------------------------------------


def _patched_oracle(result_text: str) -> Any:
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


def test_compute_subclause_dependencies_logs_banner_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """compute_subclause_dependencies prints a dependency-oracle banner."""
    with _patched_oracle("[]"):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "Dependency" in capsys.readouterr().err


def test_compute_subclause_dependencies_logs_subclause_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """compute_subclause_dependencies includes the subclause in its banner."""
    with _patched_oracle("[]"):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "§33.4" in capsys.readouterr().err


# --- build_dependency_prompt (positive instructions / f-string fix) ---------


def test_build_dependency_prompt_excludes_self_via_substituted_subclause() -> None:
    """The 'exclude self' clause names the actual subclause, not a literal placeholder."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "{subclause}" not in prompt


def test_build_dependency_prompt_avoids_uppercase_do_not() -> None:
    """The dependency oracle prompt avoids the 'Do NOT' phrasing."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "Do NOT" not in prompt


def test_build_dependency_prompt_avoids_lowercase_do_not() -> None:
    """The dependency oracle prompt avoids the 'do not' phrasing."""
    prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "do not" not in prompt


# --- run_oracle_call: retry-helper wiring -----------------------------------


def test_run_oracle_call_passes_role_to_retry_helper() -> None:
    """The Oracle role is forwarded so retry warnings name it."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert mock_stream.call_args[1]["role"] == "Oracle"


def test_run_oracle_call_retry_cmd_uses_continue() -> None:
    """The retry_cmd handed to the helper appends --continue."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--continue" in mock_stream.call_args[1]["retry_cmd"]


def test_run_oracle_call_retry_cmd_carries_model() -> None:
    """The retry_cmd uses the same model as the initial cmd."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="haiku")
    retry_cmd = mock_stream.call_args[1]["retry_cmd"]
    assert retry_cmd[retry_cmd.index("--model") + 1] == "haiku"
