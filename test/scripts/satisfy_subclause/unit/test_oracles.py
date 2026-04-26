"""Unit tests for satisfy_subclause.oracles."""

import json
from unittest.mock import patch

import pytest

from satisfy_subclause import oracles
from satisfy_subclause.oracles import (
    DISALLOWED_TOOLS,
    SATISFACTION_CONDITIONS,
    SATISFIED,
    SubclauseDiagnostic,
    build_dependency_prompt,
    build_env,
    build_satisfaction_prompt,
    compute_subclause_dependencies,
    extract_json_literal,
    is_subclause_satisfied,
    parse_dependencies,
    parse_satisfaction_diagnostic,
    run_oracle_call,
)


# --- types and constants ----------------------------------------------------


def test_satisfaction_conditions_match_predicate() -> None:
    """The five conditions correspond to the (a)-(e) satisfaction predicate."""
    assert SATISFACTION_CONDITIONS == (
        "rule_coverage", "test_coverage", "test_placement",
        "naming", "deduplication",
    )


def test_satisfied_is_the_string_satisfied() -> None:
    """The SATISFIED sentinel is the string 'satisfied'."""
    assert SATISFIED == "satisfied"


# --- SubclauseDiagnostic.verdict --------------------------------------------


def _diagnostic(**overrides) -> SubclauseDiagnostic:
    """Build a diagnostic with all conditions satisfied except overrides."""
    fields = {condition: SATISFIED for condition in SATISFACTION_CONDITIONS}
    fields.update(overrides)
    return SubclauseDiagnostic(**fields)


def test_verdict_yes_when_all_conditions_satisfied() -> None:
    """Verdict is 'yes' when every condition is satisfied."""
    assert _diagnostic().verdict == "yes"


def test_verdict_no_when_rule_coverage_fails() -> None:
    """Verdict is 'no' when rule_coverage reports failures."""
    diag = _diagnostic(rule_coverage=["rule 7 has no production code"])
    assert diag.verdict == "no"


def test_verdict_no_when_test_coverage_fails() -> None:
    """Verdict is 'no' when test_coverage reports failures."""
    diag = _diagnostic(test_coverage=["rule 5 has no test"])
    assert diag.verdict == "no"


def test_verdict_no_when_test_placement_fails() -> None:
    """Verdict is 'no' when test_placement reports failures."""
    diag = _diagnostic(test_placement=["misplaced"])
    assert diag.verdict == "no"


def test_verdict_no_when_naming_fails() -> None:
    """Verdict is 'no' when naming reports failures."""
    diag = _diagnostic(naming=["bad name"])
    assert diag.verdict == "no"


def test_verdict_no_when_deduplication_fails() -> None:
    """Verdict is 'no' when deduplication reports failures."""
    diag = _diagnostic(deduplication=["dup"])
    assert diag.verdict == "no"


def test_diagnostic_preserves_failure_list() -> None:
    """A failure list is stored verbatim and accessible by attribute."""
    failures = ["rule 7 missing", "rule 9 missing"]
    diag = _diagnostic(rule_coverage=failures)
    assert diag.rule_coverage == failures


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


def test_run_oracle_call_passes_clean_env() -> None:
    """Passes a CLAUDECODE-scrubbed env to the streaming runner."""
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        with _patched_streaming() as mock_stream:
            run_oracle_call("prompt", model="opus")
    assert "CLAUDECODE" not in mock_stream.call_args[1]["env"]


# --- build_satisfaction_prompt ---------------------------------------------


def test_build_satisfaction_prompt_mentions_subclause() -> None:
    """Prompt mentions the target subclause."""
    assert "§6.3" in build_satisfaction_prompt("6.3", "~/LRM.pdf")


def test_build_satisfaction_prompt_mentions_read_only() -> None:
    """Prompt explicitly states the oracle is read-only."""
    assert "READ-ONLY" in build_satisfaction_prompt("6.3", "~/LRM.pdf")


def test_build_satisfaction_prompt_mentions_lrm() -> None:
    """Prompt embeds the LRM path."""
    assert "~/LRM.pdf" in build_satisfaction_prompt("6.3", "~/LRM.pdf")


def test_build_satisfaction_prompt_includes_canonical_files() -> None:
    """Prompt lists at least one canonical test file for the subclause."""
    prompt = build_satisfaction_prompt("6.3", "~/LRM.pdf")
    assert "test_parser_clause_06_03.cpp" in prompt


def test_build_satisfaction_prompt_lists_all_five_conditions() -> None:
    """Prompt names all five satisfaction conditions."""
    prompt = build_satisfaction_prompt("6.3", "~/LRM.pdf")
    missing = [c for c in SATISFACTION_CONDITIONS if c not in prompt]
    assert missing == []


def test_build_satisfaction_prompt_requests_json_output() -> None:
    """Prompt instructs the oracle to output a single JSON object."""
    assert "JSON object" in build_satisfaction_prompt("6.3", "~/LRM.pdf")


def test_build_satisfaction_prompt_describes_rollup() -> None:
    """Prompt explains that parent subclauses roll up over children."""
    assert "rolls up" in build_satisfaction_prompt("33.4", "~/LRM.pdf")


def test_build_satisfaction_prompt_forbids_self_recursion() -> None:
    """Prompt forbids the oracle from invoking itself recursively."""
    assert "recursively" in build_satisfaction_prompt("33.4", "~/LRM.pdf")


def test_build_satisfaction_prompt_includes_pascalcase_naming() -> None:
    """Prompt mentions the PascalCase naming convention."""
    assert "PascalCase" in build_satisfaction_prompt("6.3", "~/LRM.pdf")


# --- parse_satisfaction_diagnostic ------------------------------------------


def test_parse_satisfaction_diagnostic_all_satisfied(
    all_satisfied_payload,
) -> None:
    """All-satisfied JSON parses into a satisfied diagnostic."""
    diag = parse_satisfaction_diagnostic(json.dumps(all_satisfied_payload))
    assert diag.verdict == "yes"


def test_parse_satisfaction_diagnostic_with_failures(
    all_satisfied_payload,
) -> None:
    """A failure list parses through to the diagnostic verbatim."""
    payload = dict(all_satisfied_payload)
    payload["rule_coverage"] = ["rule 7 missing"]
    diag = parse_satisfaction_diagnostic(json.dumps(payload))
    assert diag.rule_coverage == ["rule 7 missing"]


def test_parse_satisfaction_diagnostic_with_failures_verdict_no(
    all_satisfied_payload,
) -> None:
    """A diagnostic with any failure has verdict 'no'."""
    payload = dict(all_satisfied_payload)
    payload["test_coverage"] = ["rule 9 missing"]
    diag = parse_satisfaction_diagnostic(json.dumps(payload))
    assert diag.verdict == "no"


def test_parse_satisfaction_diagnostic_handles_fenced_json(
    all_satisfied_payload,
) -> None:
    """A fenced JSON oracle response parses."""
    text = "```json\n" + json.dumps(all_satisfied_payload) + "\n```"
    diag = parse_satisfaction_diagnostic(text)
    assert diag.verdict == "yes"


def test_parse_satisfaction_diagnostic_rejects_missing_condition(
    all_satisfied_payload,
) -> None:
    """An object missing one of the five conditions raises ValueError."""
    payload = dict(all_satisfied_payload)
    del payload["naming"]
    with pytest.raises(ValueError):
        parse_satisfaction_diagnostic(json.dumps(payload))


def test_parse_satisfaction_diagnostic_rejects_empty_list(
    all_satisfied_payload,
) -> None:
    """An empty list for a condition is invalid."""
    payload = dict(all_satisfied_payload)
    payload["rule_coverage"] = []
    with pytest.raises(ValueError):
        parse_satisfaction_diagnostic(json.dumps(payload))


def test_parse_satisfaction_diagnostic_rejects_non_string_items(
    all_satisfied_payload,
) -> None:
    """A failure list of non-strings raises ValueError."""
    payload = dict(all_satisfied_payload)
    payload["rule_coverage"] = [42]
    with pytest.raises(ValueError):
        parse_satisfaction_diagnostic(json.dumps(payload))


def test_parse_satisfaction_diagnostic_rejects_unknown_value(
    all_satisfied_payload,
) -> None:
    """A non-list, non-'satisfied' value raises ValueError."""
    payload = dict(all_satisfied_payload)
    payload["naming"] = "maybe"
    with pytest.raises(ValueError):
        parse_satisfaction_diagnostic(json.dumps(payload))


# --- is_subclause_satisfied -------------------------------------------------


def _patched_oracle(result_text):
    """Patch run_oracle_call with a fixed return string."""
    return patch(
        "satisfy_subclause.oracles.run_oracle_call",
        return_value=result_text,
    )


def test_is_subclause_satisfied_returns_yes_diagnostic(
    all_satisfied_payload,
) -> None:
    """is_subclause_satisfied returns a satisfied diagnostic when all pass."""
    payload = json.dumps(all_satisfied_payload)
    with _patched_oracle(payload):
        diag = is_subclause_satisfied("4.1", "lrm.pdf", model="opus")
    assert diag.verdict == "yes"


def test_is_subclause_satisfied_passes_model_to_oracle(
    all_satisfied_payload,
) -> None:
    """is_subclause_satisfied forwards the model arg to run_oracle_call."""
    payload = json.dumps(all_satisfied_payload)
    with _patched_oracle(payload) as mock_run:
        is_subclause_satisfied("4.1", "lrm.pdf", model="haiku")
    assert mock_run.call_args[1]["model"] == "haiku"


def test_is_subclause_satisfied_logs_banner_to_stderr(
    all_satisfied_payload, capsys,
) -> None:
    """is_subclause_satisfied prints a one-line banner to stderr."""
    payload = json.dumps(all_satisfied_payload)
    with _patched_oracle(payload):
        is_subclause_satisfied("4.1", "lrm.pdf", model="opus")
    assert "Satisfaction" in capsys.readouterr().err


def test_is_subclause_satisfied_logs_subclause_to_stderr(
    all_satisfied_payload, capsys,
) -> None:
    """is_subclause_satisfied includes the subclause in its banner."""
    payload = json.dumps(all_satisfied_payload)
    with _patched_oracle(payload):
        is_subclause_satisfied("4.1", "lrm.pdf", model="opus")
    assert "§4.1" in capsys.readouterr().err


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


def test_parse_dependencies_accepts_annex() -> None:
    """An annex-letter dependency entry is accepted."""
    assert parse_dependencies('["A.7"]') == ["A.7"]


def test_parse_dependencies_rejects_object() -> None:
    """A JSON object (not array) is rejected."""
    with pytest.raises(ValueError):
        parse_dependencies('{"deps": []}')


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


# --- compute_subclause_dependencies -----------------------------------------


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


# --- module-level imports ---------------------------------------------------


def test_oracles_module_exports_satisfaction_conditions() -> None:
    """The module exposes SATISFACTION_CONDITIONS at top level."""
    assert hasattr(oracles, "SATISFACTION_CONDITIONS")
