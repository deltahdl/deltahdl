"""Unit tests for lib.python.lrm_subclause_dependencies."""

from typing import Any
from unittest.mock import patch

import pytest

from lib.python.lrm_subclause_dependencies import (
    ORACLE_DENY_PATTERNS,
    AggregateRejection,
    build_dependency_prompt,
    build_parse_retry_prompt,
    compute_subclause_dependencies,
    parse_dependencies,
    run_oracle_call,
)


# --- ORACLE_DENY_PATTERNS ---------------------------------------------------


def test_deny_patterns_blocks_git() -> None:
    """The oracle deny list blocks git — the oracle is read-only by intent."""
    assert "git" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_gh() -> None:
    """The oracle deny list blocks gh."""
    assert "gh" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_rm() -> None:
    """The oracle deny list blocks rm."""
    assert "rm" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_mv() -> None:
    """The oracle deny list blocks mv."""
    assert "mv" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_cp() -> None:
    """The oracle deny list blocks cp."""
    assert "cp" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_touch() -> None:
    """The oracle deny list blocks touch."""
    assert "touch" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_mkdir() -> None:
    """The oracle deny list blocks mkdir."""
    assert "mkdir" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdftotext() -> None:
    """The oracle deny list blocks pdftotext."""
    assert "pdftotext" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdfgrep() -> None:
    """The oracle deny list blocks pdfgrep."""
    assert "pdfgrep" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdftohtml() -> None:
    """The oracle deny list blocks pdftohtml."""
    assert "pdftohtml" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdftoppm() -> None:
    """The oracle deny list blocks pdftoppm."""
    assert "pdftoppm" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_mutool() -> None:
    """The oracle deny list blocks mutool."""
    assert "mutool" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_python3() -> None:
    """The oracle deny list blocks python3.

    Closes the wrapper-evasion hole where sub-Claude routed a banned
    pdftotext invocation through ``python3 -c "subprocess.run(...)"``.
    """
    assert "python3" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_python() -> None:
    """The oracle deny list blocks python.

    Same wrapper hole as ``python3``, via the unsuffixed ``python``
    binary that some environments expose.
    """
    assert "python" in ORACLE_DENY_PATTERNS


# --- run_oracle_call --------------------------------------------------------


def _patched_streaming(result_text: str = "DONE") -> Any:
    """Patch run_claude_streaming with a fixed return string."""
    return patch(
        "lib.python.lrm_subclause_dependencies.run_claude_streaming_with_retry",
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


def test_run_oracle_call_passes_effort_to_cli() -> None:
    """An explicit effort flows to --effort on the Claude CLI argv."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus", effort="medium")
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--effort") + 1] == "medium"


def test_run_oracle_call_omits_effort_by_default() -> None:
    """Without an effort kwarg, --effort is absent from the Claude CLI argv."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--effort" not in mock_stream.call_args[0][0]


def test_run_oracle_call_retry_cmd_carries_effort() -> None:
    """The retry_cmd uses the same effort as the initial cmd."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus", effort="medium")
    retry_cmd = mock_stream.call_args[1]["retry_cmd"]
    assert retry_cmd[retry_cmd.index("--effort") + 1] == "medium"


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


def test_run_oracle_call_passes_settings_path() -> None:
    """Writes a temp deny-hook settings file and forwards it via --settings."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--settings" in mock_stream.call_args[0][0]


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


_EMPTY_TOC: dict[str, tuple[int, int]] = {}
_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210),
    "A": (900, 939), "A.1": (900, 919),
}
_SINGLETON_TOC: dict[str, tuple[int, int]] = {
    "2": (10, 12), "B": (940, 949),
}


def test_parse_dependencies_empty() -> None:
    """An empty array parses to an empty list."""
    assert not parse_dependencies("[]", toc=_EMPTY_TOC)


def test_parse_dependencies_single_entry() -> None:
    """A single subclause string parses through verbatim."""
    assert parse_dependencies('["33.6.1"]', toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_preserves_order() -> None:
    """Dependencies are returned in the order the oracle listed them."""
    text = '["33.6.1", "33.4.1.5", "33.4.1.6"]'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == [
        "33.6.1", "33.4.1.5", "33.4.1.6",
    ]


def test_parse_dependencies_handles_fenced_array() -> None:
    """A fenced JSON array oracle response parses."""
    text = '```json\n["33.6.1"]\n```'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_handles_unmarked_fence() -> None:
    """A bare ``` fence (no language) parses."""
    text = '```\n["33.6.1"]\n```'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_handles_text_before_array() -> None:
    """A bare array surrounded by prose parses."""
    text = 'preamble ["33.6.1"] trailer'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_accepts_annex() -> None:
    """An annex-letter dependency entry is accepted."""
    assert parse_dependencies('["A.7"]', toc=_EMPTY_TOC) == ["A.7"]


def test_parse_dependencies_rejects_non_string_entry() -> None:
    """A non-string entry in the array is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('[42]', toc=_EMPTY_TOC)


def test_parse_dependencies_rejects_garbage_entry() -> None:
    """An entry that is not a valid clause identifier is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('["not-a-clause"]', toc=_EMPTY_TOC)


def test_parse_dependencies_rejects_lowercase_letter() -> None:
    """A lowercase letter clause is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('["a.7"]', toc=_EMPTY_TOC)


def test_parse_dependencies_rejects_text_without_array() -> None:
    """Output without a JSON array raises ValueError."""
    with pytest.raises(ValueError):
        parse_dependencies("no array here", toc=_EMPTY_TOC)


def test_parse_dependencies_picks_last_array_when_prose_has_brackets() -> None:
    """Prose containing a bracketed example doesn't swallow the real array."""
    text = (
        "Reasoning: §3.9 says [example with typedef struct, function].\n\n"
        "It defers all syntax to Clause 26.\n\n"
        "[]"
    )
    assert not parse_dependencies(text, toc=_EMPTY_TOC)


def test_parse_dependencies_picks_last_nonempty_array_when_prose_has_brackets() -> None:
    """A non-empty final array is picked over earlier bracketed prose."""
    text = (
        "Earlier prose [unrelated bracketed text] more prose.\n\n"
        '["33.6.1", "33.4.1.5"]'
    )
    assert parse_dependencies(text, toc=_EMPTY_TOC) == [
        "33.6.1", "33.4.1.5",
    ]


def test_parse_dependencies_rejects_aggregate_chapter_identifier() -> None:
    """An identifier naming an aggregate top-level chapter is rejected."""
    with pytest.raises(AggregateRejection):
        parse_dependencies('["8"]', toc=_AGGREGATE_TOC)


def test_parse_dependencies_aggregate_chapter_rejection_carries_identifier() -> None:
    """The aggregate-chapter rejection exposes the rejected identifier."""
    captured: str | None = None
    try:
        parse_dependencies('["8"]', toc=_AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifier
    assert captured == "8"


def test_parse_dependencies_rejects_aggregate_annex_identifier() -> None:
    """An identifier naming an aggregate annex is rejected."""
    with pytest.raises(AggregateRejection):
        parse_dependencies('["A"]', toc=_AGGREGATE_TOC)


def test_parse_dependencies_aggregate_annex_rejection_carries_identifier() -> None:
    """The aggregate-annex rejection exposes the rejected identifier."""
    captured: str | None = None
    try:
        parse_dependencies('["A"]', toc=_AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifier
    assert captured == "A"


def test_parse_dependencies_raises_plain_value_error_for_bad_shape() -> None:
    """A non-aggregate shape failure stays a plain ValueError, not an AggregateRejection."""
    captured: ValueError | None = None
    try:
        parse_dependencies('["not-a-clause"]', toc=_AGGREGATE_TOC)
    except ValueError as exc:
        captured = exc
    assert not isinstance(captured, AggregateRejection)


def test_parse_dependencies_accepts_singleton_chapter() -> None:
    """A top-level chapter that is a singleton (no numbered subs) is accepted."""
    assert parse_dependencies('["2"]', toc=_SINGLETON_TOC) == ["2"]


def test_parse_dependencies_accepts_singleton_annex() -> None:
    """A childless annex (Annex B / P / Q) is accepted as a dep."""
    assert parse_dependencies('["B"]', toc=_SINGLETON_TOC) == ["B"]


def test_parse_dependencies_accepts_sub_level_under_aggregate() -> None:
    """A sub-level entry under an aggregate parent is accepted."""
    assert parse_dependencies('["8.1"]', toc=_AGGREGATE_TOC) == ["8.1"]


# --- compute_subclause_dependencies -----------------------------------------


def _patched_oracle(result_text: str) -> Any:
    """Patch run_oracle_call with a fixed return string."""
    return patch(
        "lib.python.lrm_subclause_dependencies.run_oracle_call",
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


def test_compute_subclause_dependencies_passes_effort() -> None:
    """compute_subclause_dependencies forwards the effort arg."""
    with _patched_oracle("[]") as mock_run:
        compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus", effort="medium",
        )
    assert mock_run.call_args[1]["effort"] == "medium"


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


def test_compute_subclause_dependencies_exits_when_aggregate_output_persists() -> None:
    """An aggregate identifier returned every retry exits after the budget is exhausted."""
    aggregate_toc = {"8": (200, 250), "8.1": (200, 210)}
    with _patched_oracle('["8"]'), patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=aggregate_toc,
    ):
        with pytest.raises(SystemExit):
            compute_subclause_dependencies(
                "33.4", "lrm.pdf", model="opus",
            )


def test_compute_subclause_dependencies_loads_toc_from_lrm_path() -> None:
    """compute_subclause_dependencies passes the --lrm path through to load_toc."""
    with _patched_oracle("[]"), patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value={},
    ) as mock_toc:
        compute_subclause_dependencies(
            "33.4", "/tmp/spec.pdf", model="opus",
        )
    assert mock_toc.call_args[0][0] == "/tmp/spec.pdf"


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


# --- build_dependency_prompt: sub-level-parent branch -----------------------


_PARENT_TOC: dict[str, tuple[int, int]] = {
    "33.4": (100, 200), "33.4.1": (100, 110),
}


def test_build_dependency_prompt_sub_level_parent_mentions_preamble() -> None:
    """A sub-level parent's prompt anchors the rules in the parent's preamble."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "preamble" in prompt


def test_build_dependency_prompt_sub_level_parent_signals_subclauses_separate() -> None:
    """A sub-level parent's prompt names that numbered subclauses are queried separately."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "queried separately" in prompt


def test_build_dependency_prompt_sub_level_parent_grounds_in_normative_rule() -> None:
    """A sub-level parent's prompt still requires a normative-rule grounding."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "normative rule" in prompt


def test_build_dependency_prompt_sub_level_parent_keeps_machinery_anchor() -> None:
    """A sub-level parent's prompt keeps the §Y-machinery prerequisite anchor."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "machinery" in prompt


def test_build_dependency_prompt_sub_level_parent_keeps_json_array() -> None:
    """A sub-level parent's prompt still requests a JSON array."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "JSON array" in prompt


def test_build_dependency_prompt_sub_level_parent_avoids_do_not() -> None:
    """A sub-level parent's prompt avoids the 'do not' phrasing."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/LRM.pdf")
    assert "do not" not in prompt


def test_build_dependency_prompt_leaf_omits_preamble() -> None:
    """A leaf target's prompt does not branch into the preamble framing."""
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value={},
    ):
        prompt = build_dependency_prompt("33.4.1.5", "~/LRM.pdf")
    assert "preamble" not in prompt


def test_build_dependency_prompt_top_level_singleton_omits_preamble() -> None:
    """A top-level singleton like §2 is not a parent and gets the leaf prompt."""
    singleton_toc = {"2": (10, 12)}
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=singleton_toc,
    ):
        prompt = build_dependency_prompt("2", "~/LRM.pdf")
    assert "preamble" not in prompt


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


# --- run_oracle_call: continue_session opt-in -------------------------------


def test_run_oracle_call_initial_cmd_uses_continue_when_opted_in() -> None:
    """continue_session=True puts --continue into the initial Claude CLI argv."""
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus", continue_session=True)
    assert "--continue" in mock_stream.call_args[0][0]


# --- compute_subclause_dependencies: parse-failure retry --------------------


_RETRY_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "8": (200, 250), "8.1": (200, 210),
}


def _patched_oracle_sequence(*results: str) -> Any:
    """Patch run_oracle_call so each invocation returns the next *results* item."""
    return patch(
        "lib.python.lrm_subclause_dependencies.run_oracle_call",
        side_effect=list(results),
    )


def _patched_retry_toc() -> Any:
    """Patch load_toc so the aggregate-rejection branch fires on '["8"]'."""
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_RETRY_AGGREGATE_TOC,
    )


def test_compute_subclause_dependencies_retries_on_parse_failure() -> None:
    """A rejected oracle response triggers a follow-up run_oracle_call."""
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert mock_run.call_count == 2


def test_compute_subclause_dependencies_retry_resumes_session() -> None:
    """The retry call sets continue_session=True so it resumes the same session."""
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert mock_run.call_args_list[1].kwargs["continue_session"] is True


def test_compute_subclause_dependencies_retry_prompt_quotes_offender() -> None:
    """The corrective prompt names the offending entry from the rejection message."""
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "'8'" in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_prompt_carries_model() -> None:
    """The retry call forwards the same model as the initial call."""
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="haiku")
    assert mock_run.call_args_list[1].kwargs["model"] == "haiku"


def test_compute_subclause_dependencies_retry_prompt_carries_effort() -> None:
    """The retry call forwards the same effort as the initial call."""
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus", effort="medium",
        )
    assert mock_run.call_args_list[1].kwargs["effort"] == "medium"


def test_compute_subclause_dependencies_returns_after_successful_retry() -> None:
    """A clean array on the retry call is returned to the caller."""
    with _patched_oracle_sequence('["8"]', '["33.6.1"]'), _patched_retry_toc():
        deps = compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus",
        )
    assert deps == ["33.6.1"]


def test_compute_subclause_dependencies_logs_retry_warning_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A retry attempt logs a WARNING line to stderr."""
    with _patched_oracle_sequence('["8"]', "[]"), _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "WARNING" in capsys.readouterr().err


def test_compute_subclause_dependencies_recovers_from_invalid_json() -> None:
    """A malformed-JSON response is also a recoverable parse failure."""
    with _patched_oracle_sequence("not an array", "[]") as mock_run, patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value={},
    ):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert mock_run.call_count == 2


# --- AggregateRejection -----------------------------------------------------


def test_aggregate_rejection_subclass_of_value_error() -> None:
    """AggregateRejection is a ValueError so existing handlers still catch it."""
    assert issubclass(AggregateRejection, ValueError)


def test_aggregate_rejection_carries_identifier() -> None:
    """AggregateRejection stores the rejected identifier as ``.identifier``."""
    exc = AggregateRejection("13", "Dependency entry '13' names an aggregate...")
    assert exc.identifier == "13"


def test_aggregate_rejection_str_returns_message() -> None:
    """str(AggregateRejection) returns the message, preserving prior callers."""
    exc = AggregateRejection("13", "the message")
    assert str(exc) == "the message"


# --- build_parse_retry_prompt -----------------------------------------------


def test_build_parse_retry_prompt_without_alternatives_quotes_reason() -> None:
    """With no alternatives, the corrective prompt embeds the rejection reason."""
    prompt = build_parse_retry_prompt("bad shape '13'")
    assert "bad shape '13'" in prompt


def test_build_parse_retry_prompt_without_alternatives_keeps_baseline_phrase() -> None:
    """The non-aggregate baseline wording survives the optional-param refactor."""
    prompt = build_parse_retry_prompt("reason")
    assert "JSON array" in prompt


def test_build_parse_retry_prompt_lists_first_alternative() -> None:
    """The first supplied alternative identifier appears in the corrective prompt."""
    prompt = build_parse_retry_prompt(
        "reason", aggregate="13", alternatives=["13.3", "13.4", "13.5"],
    )
    assert "13.3" in prompt


def test_build_parse_retry_prompt_lists_middle_alternative() -> None:
    """A middle supplied alternative identifier appears in the corrective prompt."""
    prompt = build_parse_retry_prompt(
        "reason", aggregate="13", alternatives=["13.3", "13.4", "13.5"],
    )
    assert "13.4" in prompt


def test_build_parse_retry_prompt_lists_last_alternative() -> None:
    """The last supplied alternative identifier appears in the corrective prompt."""
    prompt = build_parse_retry_prompt(
        "reason", aggregate="13", alternatives=["13.3", "13.4", "13.5"],
    )
    assert "13.5" in prompt


def test_build_parse_retry_prompt_names_rejected_aggregate() -> None:
    """The aggregate-branch prompt quotes the rejected aggregate identifier."""
    prompt = build_parse_retry_prompt(
        "reason", aggregate="13", alternatives=["13.1"],
    )
    assert "'13'" in prompt


def test_build_parse_retry_prompt_allows_plural_replacement() -> None:
    """The aggregate-branch prompt invites listing more than one subclause."""
    prompt = build_parse_retry_prompt(
        "reason", aggregate="13", alternatives=["13.3", "13.4"],
    )
    assert "list all of them" in prompt


def test_build_parse_retry_prompt_aggregate_branch_keeps_reason() -> None:
    """The aggregate-branch prompt also embeds the rejection reason."""
    prompt = build_parse_retry_prompt(
        "the reason", aggregate="13", alternatives=["13.1"],
    )
    assert "the reason" in prompt


# --- compute_subclause_dependencies: aggregate-retry enumeration ------------


_ENUM_TOC: dict[str, tuple[int, int]] = {
    "13": (336, 354),
    "13.1": (336, 336), "13.2": (336, 336), "13.3": (336, 340),
    "13.4": (341, 347), "13.5": (348, 352), "13.6": (353, 353),
    "13.7": (353, 353), "13.8": (353, 354),
}


def _patched_enum_toc() -> Any:
    """Patch load_toc so the aggregate-retry enumeration uses _ENUM_TOC."""
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_ENUM_TOC,
    )


def test_compute_subclause_dependencies_retry_prompt_enumerates_first_child() -> None:
    """The aggregate-retry prompt names the first numbered subclause under the aggregate."""
    with _patched_oracle_sequence('["13"]', "[]") as mock_run, _patched_enum_toc():
        compute_subclause_dependencies("18.17", "lrm.pdf", model="opus")
    assert "13.3" in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_prompt_enumerates_other_child() -> None:
    """The aggregate-retry prompt lists another numbered subclause under the rejected aggregate."""
    with _patched_oracle_sequence('["13"]', "[]") as mock_run, _patched_enum_toc():
        compute_subclause_dependencies("18.17", "lrm.pdf", model="opus")
    assert "13.4" in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_prompt_skips_enumeration_for_bad_json() -> None:
    """A non-aggregate (bad-JSON) failure does NOT enumerate any TOC children."""
    with _patched_oracle_sequence("not an array", "[]") as mock_run, patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_ENUM_TOC,
    ):
        compute_subclause_dependencies("18.17", "lrm.pdf", model="opus")
    assert "list all of them" not in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_succeeds_after_aggregate_split() -> None:
    """An aggregate rejection followed by a plural-split answer satisfies the call."""
    with _patched_oracle_sequence(
        '["13"]', '["13.3", "13.4"]',
    ), _patched_enum_toc():
        deps = compute_subclause_dependencies(
            "18.17", "lrm.pdf", model="opus",
        )
    assert deps == ["13.3", "13.4"]
