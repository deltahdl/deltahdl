import json
from typing import Any
from unittest.mock import patch

import pytest

from lib.python.claude_cli_streaming import deny_bash_hook as hook
from lib.python.lrm_subclause_dependencies import (
    ORACLE_DENY_PATTERNS,
    AggregateRejection,
    build_dependency_prompt,
    build_parse_retry_prompt,
    compute_subclause_dependencies,
    parse_dependencies,
    run_oracle_call,
    validate_dependencies,
)
from lib.python.test_fixtures.lrm_subclause_dependencies import (
    AGGREGATE_TOC as _AGGREGATE_TOC,
    patched_oracle_sequence as _patched_oracle_sequence,
    patched_retry_toc as _patched_retry_toc,
)


def test_deny_patterns_blocks_git() -> None:
    assert "git" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_gh() -> None:
    assert "gh" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_rm() -> None:
    assert "rm" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_mv() -> None:
    assert "mv" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_cp() -> None:
    assert "cp" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_touch() -> None:
    assert "touch" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_mkdir() -> None:
    assert "mkdir" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdftotext() -> None:
    assert "pdftotext" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdfgrep() -> None:
    assert "pdfgrep" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdftohtml() -> None:
    assert "pdftohtml" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_pdftoppm() -> None:
    assert "pdftoppm" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_mutool() -> None:
    assert "mutool" in ORACLE_DENY_PATTERNS


def _blocked(command: str) -> bool:
    event = json.dumps({"tool_name": "Bash", "tool_input": {"command": command}})
    return hook.match_deny_pattern(event, ORACLE_DENY_PATTERNS) is not None


def test_deny_patterns_blocks_python3() -> None:
    assert _blocked('python3 -c "import subprocess"')


def test_deny_patterns_blocks_versioned_python() -> None:
    assert _blocked("python3.13 script.py")


def test_deny_patterns_blocks_python() -> None:
    assert "python" in ORACLE_DENY_PATTERNS


def test_deny_patterns_blocks_oracle_build() -> None:
    assert _blocked("cmake -S . -B build-oracle")


def _patched_streaming(result_text: str = "DONE") -> Any:
    return patch(
        "lib.python.lrm_subclause_dependencies.run_claude_streaming_with_retry",
        return_value=result_text,
    )


def test_run_oracle_call_returns_result_text() -> None:
    with _patched_streaming("DONE"):
        assert run_oracle_call("prompt", model="opus") == "DONE"


def test_run_oracle_call_passes_prompt() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("hello prompt", model="opus")
    assert mock_stream.call_args[0][1] == "hello prompt"


def test_run_oracle_call_passes_model_to_cli() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="haiku")
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_oracle_call_passes_effort_to_cli() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus", effort="medium")
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--effort") + 1] == "medium"


def test_run_oracle_call_omits_effort_by_default() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--effort" not in mock_stream.call_args[0][0]


def test_run_oracle_call_retry_cmd_carries_effort() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus", effort="medium")
    retry_cmd = mock_stream.call_args[1]["retry_cmd"]
    assert retry_cmd[retry_cmd.index("--effort") + 1] == "medium"


def test_run_oracle_call_uses_stream_json() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_run_oracle_call_uses_verbose() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--verbose" in mock_stream.call_args[0][0]


def test_run_oracle_call_passes_settings_path() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--settings" in mock_stream.call_args[0][0]


def test_run_oracle_call_uses_dangerously_skip_permissions() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--dangerously-skip-permissions" in mock_stream.call_args[0][0]


def test_run_oracle_call_does_not_continue_session() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--continue" not in mock_stream.call_args[0][0]


def test_run_oracle_call_passes_clean_env() -> None:
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        with _patched_streaming() as mock_stream:
            run_oracle_call("prompt", model="opus")
    assert "CLAUDECODE" not in mock_stream.call_args[1]["env"]


def test_build_dependency_prompt_mentions_subclause() -> None:
    assert "§33.4.1.5" in build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")


def test_build_dependency_prompt_mentions_read_only() -> None:
    assert "read-only" in build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")


def test_build_dependency_prompt_mentions_lrm() -> None:
    assert "~/IEEE 1800-2023.pdf" in build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")


def test_build_dependency_prompt_grounds_in_normative_rule() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "normative rule" in prompt


def test_build_dependency_prompt_anchors_dep_on_machinery_prereq() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "machinery" in prompt


def test_build_dependency_prompt_invites_quotable_evidence() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "quote" in prompt


def test_build_dependency_prompt_drops_term_use_criterion() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "term, function, or syntactic construct" not in prompt


def test_build_dependency_prompt_orders_foundations_first() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "foundations-first" in prompt


def test_build_dependency_prompt_avoids_required_emphasis() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "REQUIRED" not in prompt


def test_build_dependency_prompt_drops_parent_rollup_rule() -> None:
    prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "rolls up" not in prompt


def test_build_dependency_prompt_requests_json_array() -> None:
    assert "JSON array" in build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")


def test_build_dependency_prompt_says_empty_if_none() -> None:
    assert "[]" in build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")


_EMPTY_TOC: dict[str, tuple[int, int]] = {}
_SINGLETON_TOC: dict[str, tuple[int, int]] = {
    "2": (10, 12), "B": (940, 949),
}


def test_parse_dependencies_empty() -> None:
    assert not parse_dependencies("[]", toc=_EMPTY_TOC)


def test_parse_dependencies_single_entry() -> None:
    assert parse_dependencies('["33.6.1"]', toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_preserves_order() -> None:
    text = '["33.6.1", "33.4.1.5", "33.4.1.6"]'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == [
        "33.6.1", "33.4.1.5", "33.4.1.6",
    ]


def test_parse_dependencies_handles_fenced_array() -> None:
    text = '```json\n["33.6.1"]\n```'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_handles_unmarked_fence() -> None:
    text = '```\n["33.6.1"]\n```'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_handles_text_before_array() -> None:
    text = 'preamble ["33.6.1"] trailer'
    assert parse_dependencies(text, toc=_EMPTY_TOC) == ["33.6.1"]


def test_parse_dependencies_accepts_annex() -> None:
    assert parse_dependencies('["A.7"]', toc=_EMPTY_TOC) == ["A.7"]


def test_parse_dependencies_rejects_non_string_entry() -> None:
    with pytest.raises(ValueError):
        parse_dependencies('[42]', toc=_EMPTY_TOC)


def test_parse_dependencies_rejects_garbage_entry() -> None:
    with pytest.raises(ValueError):
        parse_dependencies('["not-a-clause"]', toc=_EMPTY_TOC)


def test_parse_dependencies_rejects_lowercase_letter() -> None:
    with pytest.raises(ValueError):
        parse_dependencies('["a.7"]', toc=_EMPTY_TOC)


def test_parse_dependencies_rejects_text_without_array() -> None:
    with pytest.raises(ValueError):
        parse_dependencies("no array here", toc=_EMPTY_TOC)


def test_parse_dependencies_picks_last_array_when_prose_has_brackets() -> None:
    text = (
        "Reasoning: §3.9 says [example with typedef struct, function].\n\n"
        "It defers all syntax to Clause 26.\n\n"
        "[]"
    )
    assert not parse_dependencies(text, toc=_EMPTY_TOC)


def test_parse_dependencies_picks_last_nonempty_array_when_prose_has_brackets() -> None:
    text = (
        "Earlier prose [unrelated bracketed text] more prose.\n\n"
        '["33.6.1", "33.4.1.5"]'
    )
    assert parse_dependencies(text, toc=_EMPTY_TOC) == [
        "33.6.1", "33.4.1.5",
    ]


def test_parse_dependencies_rejects_aggregate_chapter_identifier() -> None:
    with pytest.raises(AggregateRejection):
        parse_dependencies('["8"]', toc=_AGGREGATE_TOC)


def test_parse_dependencies_aggregate_chapter_rejection_carries_identifier() -> None:
    captured: list[str] | None = None
    try:
        parse_dependencies('["8"]', toc=_AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["8"]


def test_parse_dependencies_rejects_aggregate_annex_identifier() -> None:
    with pytest.raises(AggregateRejection):
        parse_dependencies('["A"]', toc=_AGGREGATE_TOC)


def test_parse_dependencies_aggregate_annex_rejection_carries_identifier() -> None:
    captured: list[str] | None = None
    try:
        parse_dependencies('["A"]', toc=_AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["A"]


def test_parse_dependencies_raises_plain_value_error_for_bad_shape() -> None:
    captured: ValueError | None = None
    try:
        parse_dependencies('["not-a-clause"]', toc=_AGGREGATE_TOC)
    except ValueError as exc:
        captured = exc
    assert not isinstance(captured, AggregateRejection)


def test_parse_dependencies_accepts_singleton_chapter() -> None:
    assert parse_dependencies('["2"]', toc=_SINGLETON_TOC) == ["2"]


def test_parse_dependencies_accepts_singleton_annex() -> None:
    assert parse_dependencies('["B"]', toc=_SINGLETON_TOC) == ["B"]


def test_parse_dependencies_accepts_sub_level_under_aggregate() -> None:
    assert parse_dependencies('["8.1"]', toc=_AGGREGATE_TOC) == ["8.1"]


def _patched_oracle(result_text: str) -> Any:
    return patch(
        "lib.python.lrm_subclause_dependencies.run_oracle_call",
        return_value=result_text,
    )


def test_compute_subclause_dependencies_returns_list() -> None:
    with _patched_oracle('["33.6.1"]'):
        deps = compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus",
        )
    assert deps == ["33.6.1"]


def test_compute_subclause_dependencies_passes_model() -> None:
    with _patched_oracle("[]") as mock_run:
        compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="haiku",
        )
    assert mock_run.call_args[1]["model"] == "haiku"


def test_compute_subclause_dependencies_passes_effort() -> None:
    with _patched_oracle("[]") as mock_run:
        compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus", effort="medium",
        )
    assert mock_run.call_args[1]["effort"] == "medium"


def test_compute_subclause_dependencies_logs_banner_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with _patched_oracle("[]"):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "Dependency" in capsys.readouterr().err


def test_compute_subclause_dependencies_logs_subclause_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with _patched_oracle("[]"):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "§33.4" in capsys.readouterr().err


def test_compute_subclause_dependencies_exits_when_aggregate_output_persists() -> None:
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
    with _patched_oracle("[]"), patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value={},
    ) as mock_toc:
        compute_subclause_dependencies(
            "33.4", "/tmp/spec.pdf", model="opus",
        )
    assert mock_toc.call_args[0][0] == "/tmp/spec.pdf"


def test_build_dependency_prompt_excludes_self_via_substituted_subclause() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "{subclause}" not in prompt


def test_build_dependency_prompt_avoids_uppercase_do_not() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "Do NOT" not in prompt


def test_build_dependency_prompt_avoids_lowercase_do_not() -> None:
    prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "do not" not in prompt


_PARENT_TOC: dict[str, tuple[int, int]] = {
    "33.4": (100, 200), "33.4.1": (100, 110),
}


def test_build_dependency_prompt_sub_level_parent_mentions_preamble() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "preamble" in prompt


def test_build_dependency_prompt_sub_level_parent_signals_subclauses_separate() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "queried separately" in prompt


def test_build_dependency_prompt_sub_level_parent_grounds_in_normative_rule() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "normative rule" in prompt


def test_build_dependency_prompt_sub_level_parent_keeps_machinery_anchor() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "machinery" in prompt


def test_build_dependency_prompt_sub_level_parent_keeps_json_array() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "JSON array" in prompt


def test_build_dependency_prompt_sub_level_parent_avoids_do_not() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_PARENT_TOC,
    ):
        prompt = build_dependency_prompt("33.4", "~/IEEE 1800-2023.pdf")
    assert "do not" not in prompt


def test_build_dependency_prompt_leaf_omits_preamble() -> None:
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value={},
    ):
        prompt = build_dependency_prompt("33.4.1.5", "~/IEEE 1800-2023.pdf")
    assert "preamble" not in prompt


def test_build_dependency_prompt_top_level_singleton_omits_preamble() -> None:
    singleton_toc = {"2": (10, 12)}
    with patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=singleton_toc,
    ):
        prompt = build_dependency_prompt("2", "~/IEEE 1800-2023.pdf")
    assert "preamble" not in prompt


def test_run_oracle_call_passes_role_to_retry_helper() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert mock_stream.call_args[1]["role"] == "Oracle"


def test_run_oracle_call_retry_cmd_uses_continue() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus")
    assert "--continue" in mock_stream.call_args[1]["retry_cmd"]


def test_run_oracle_call_retry_cmd_carries_model() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="haiku")
    retry_cmd = mock_stream.call_args[1]["retry_cmd"]
    assert retry_cmd[retry_cmd.index("--model") + 1] == "haiku"


def test_run_oracle_call_initial_cmd_uses_continue_when_opted_in() -> None:
    with _patched_streaming() as mock_stream:
        run_oracle_call("prompt", model="opus", continue_session=True)
    assert "--continue" in mock_stream.call_args[0][0]


def test_compute_subclause_dependencies_retries_on_parse_failure() -> None:
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert mock_run.call_count == 2


def test_compute_subclause_dependencies_retry_resumes_session() -> None:
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert mock_run.call_args_list[1].kwargs["continue_session"] is True


def test_compute_subclause_dependencies_retry_prompt_quotes_offender() -> None:
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "'8'" in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_prompt_carries_model() -> None:
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="haiku")
    assert mock_run.call_args_list[1].kwargs["model"] == "haiku"


def test_compute_subclause_dependencies_retry_prompt_carries_effort() -> None:
    with _patched_oracle_sequence('["8"]', "[]") as mock_run, _patched_retry_toc():
        compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus", effort="medium",
        )
    assert mock_run.call_args_list[1].kwargs["effort"] == "medium"


def test_compute_subclause_dependencies_returns_after_successful_retry() -> None:
    with _patched_oracle_sequence('["8"]', '["33.6.1"]'), _patched_retry_toc():
        deps = compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus",
        )
    assert deps == ["33.6.1"]


def test_compute_subclause_dependencies_logs_retry_warning_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with _patched_oracle_sequence('["8"]', "[]"), _patched_retry_toc():
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert "WARNING" in capsys.readouterr().err


def test_compute_subclause_dependencies_recovers_from_invalid_json() -> None:
    with _patched_oracle_sequence("not an array", "[]") as mock_run, patch(
        "lib.python.lrm_subclause_dependencies.load_toc", return_value={},
    ):
        compute_subclause_dependencies("33.4", "lrm.pdf", model="opus")
    assert mock_run.call_count == 2


def test_aggregate_rejection_subclass_of_value_error() -> None:
    assert issubclass(AggregateRejection, ValueError)


def test_aggregate_rejection_carries_identifiers_list() -> None:
    exc = AggregateRejection(
        ["13"], "Dependency entry '13' names an aggregate...",
    )
    assert exc.identifiers == ["13"]


def test_aggregate_rejection_str_returns_message() -> None:
    exc = AggregateRejection(["13"], "the message")
    assert str(exc) == "the message"


def test_build_parse_retry_prompt_without_alternatives_quotes_reason() -> None:
    prompt = build_parse_retry_prompt("bad shape '13'")
    assert "bad shape '13'" in prompt


def test_build_parse_retry_prompt_without_alternatives_keeps_baseline_phrase() -> None:
    prompt = build_parse_retry_prompt("reason")
    assert "JSON array" in prompt


def test_build_parse_retry_prompt_lists_first_alternative() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13"],
        alternatives_map={"13": ["13.3", "13.4", "13.5"]},
    )
    assert "13.3" in prompt


def test_build_parse_retry_prompt_lists_middle_alternative() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13"],
        alternatives_map={"13": ["13.3", "13.4", "13.5"]},
    )
    assert "13.4" in prompt


def test_build_parse_retry_prompt_lists_last_alternative() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13"],
        alternatives_map={"13": ["13.3", "13.4", "13.5"]},
    )
    assert "13.5" in prompt


def test_build_parse_retry_prompt_names_rejected_aggregate() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13"], alternatives_map={"13": ["13.1"]},
    )
    assert "'13'" in prompt


def test_build_parse_retry_prompt_allows_plural_replacement() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13"],
        alternatives_map={"13": ["13.3", "13.4"]},
    )
    assert "list all of them" in prompt


def test_build_parse_retry_prompt_aggregate_branch_keeps_reason() -> None:
    prompt = build_parse_retry_prompt(
        "the reason", aggregates=["13"], alternatives_map={"13": ["13.1"]},
    )
    assert "the reason" in prompt


_ENUM_TOC: dict[str, tuple[int, int]] = {
    "13": (336, 354),
    "13.1": (336, 336), "13.2": (336, 336), "13.3": (336, 340),
    "13.4": (341, 347), "13.5": (348, 352), "13.6": (353, 353),
    "13.7": (353, 353), "13.8": (353, 354),
}


def _patched_enum_toc() -> Any:
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_ENUM_TOC,
    )


def test_compute_subclause_dependencies_retry_prompt_enumerates_first_child() -> None:
    with _patched_oracle_sequence('["13"]', "[]") as mock_run, _patched_enum_toc():
        compute_subclause_dependencies("18.17", "lrm.pdf", model="opus")
    assert "13.3" in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_prompt_enumerates_other_child() -> None:
    with _patched_oracle_sequence('["13"]', "[]") as mock_run, _patched_enum_toc():
        compute_subclause_dependencies("18.17", "lrm.pdf", model="opus")
    assert "13.4" in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_prompt_skips_enumeration_for_bad_json() -> None:
    with _patched_oracle_sequence("not an array", "[]") as mock_run, patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_ENUM_TOC,
    ):
        compute_subclause_dependencies("18.17", "lrm.pdf", model="opus")
    assert "list all of them" not in mock_run.call_args_list[1].args[0]


def test_compute_subclause_dependencies_retry_succeeds_after_aggregate_split() -> None:
    with _patched_oracle_sequence(
        '["13"]', '["13.3", "13.4"]',
    ), _patched_enum_toc():
        deps = compute_subclause_dependencies(
            "18.17", "lrm.pdf", model="opus",
        )
    assert deps == ["13.3", "13.4"]


def test_validate_dependencies_accepts_a_decoded_array() -> None:
    assert validate_dependencies(["33.6.1"], toc=_EMPTY_TOC) == ["33.6.1"]


def test_validate_dependencies_accepts_an_empty_decoded_array() -> None:
    assert not validate_dependencies([], toc=_EMPTY_TOC)


def test_validate_dependencies_rejects_a_malformed_identifier() -> None:
    with pytest.raises(ValueError):
        validate_dependencies(["not-a-clause"], toc=_EMPTY_TOC)


def test_validate_dependencies_rejects_an_aggregate_identifier() -> None:
    with pytest.raises(AggregateRejection):
        validate_dependencies(["8"], toc=_AGGREGATE_TOC)
