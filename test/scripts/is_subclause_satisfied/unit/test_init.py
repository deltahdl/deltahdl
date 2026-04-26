"""Unit tests for is_subclause_satisfied (oracle script)."""

import json
import runpy
from unittest.mock import MagicMock, patch

import pytest

from lib.python.satisfy import (
    SATISFACTION_CONDITIONS,
    SATISFIED,
    SubclauseDiagnostic,
)


# ---- helpers ----------------------------------------------------------------


def _make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


_BASE_ARGS = ["--subclause", "4.1"]


def _args_with_lrm(tmp_path, *extra):
    """Return CLI args with --lrm pointing at a temp file."""
    return ["--lrm", str(_make_lrm(tmp_path)), *_BASE_ARGS, *extra]


def _all_satisfied_payload():
    """Return a payload dict with all five conditions satisfied."""
    return {condition: SATISFIED for condition in SATISFACTION_CONDITIONS}


def _claude_response(payload):
    """Return a stubbed Claude --output-format json stdout for *payload*."""
    return json.dumps({"result": json.dumps(payload)})


def _claude_completed(stdout, *, returncode=0, stderr=""):
    """Return a stubbed CompletedProcess for subprocess.run."""
    completed = MagicMock()
    completed.returncode = returncode
    completed.stdout = stdout
    completed.stderr = stderr
    return completed


# ---- parse_args -------------------------------------------------------------


def test_parse_args_requires_subclause(iss, tmp_path):
    """--subclause is required; omitting it exits."""
    with pytest.raises(SystemExit):
        iss.parse_args(["--lrm", str(_make_lrm(tmp_path))])


def test_parse_args_requires_lrm(iss):
    """--lrm is required; omitting it exits."""
    with pytest.raises(SystemExit):
        iss.parse_args(["--subclause", "4.1"])


def test_parse_args_rejects_missing_lrm(iss, tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        iss.parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--subclause", "4.1",
        ])


def test_parse_args_rejects_bad_clause(iss, tmp_path):
    """Invalid clause format exits."""
    with pytest.raises(SystemExit):
        iss.parse_args(_args_with_lrm(tmp_path)[:2] + [
            "--subclause", "bad",
        ])


def test_parse_args_accepts_numeric(iss, tmp_path):
    """Numeric clause is accepted and stored on the namespace."""
    args = iss.parse_args(_args_with_lrm(tmp_path))
    assert args.subclause == "4.1"


def test_parse_args_accepts_annex(iss, tmp_path):
    """Single-letter annex clause is accepted."""
    args = iss.parse_args([
        "--lrm", str(_make_lrm(tmp_path)), "--subclause", "B",
    ])
    assert args.subclause == "B"


def test_parse_args_accepts_deep_clause(iss, tmp_path):
    """Five-component clause is accepted."""
    args = iss.parse_args([
        "--lrm", str(_make_lrm(tmp_path)), "--subclause", "33.4.1.5.2",
    ])
    assert args.subclause == "33.4.1.5.2"


def test_parse_args_default_model(iss, tmp_path):
    """--model defaults to 'opus'."""
    args = iss.parse_args(_args_with_lrm(tmp_path))
    assert args.model == "opus"


def test_parse_args_model_override(iss, tmp_path):
    """--model accepts an override value."""
    args = iss.parse_args(_args_with_lrm(tmp_path, "--model", "sonnet"))
    assert args.model == "sonnet"


def test_parse_args_lrm_value(iss, tmp_path):
    """--lrm value is stored on the namespace."""
    args = iss.parse_args(_args_with_lrm(tmp_path))
    assert str(args.lrm) == str(_make_lrm(tmp_path))


# ---- build_prompt ----------------------------------------------------------


def test_build_prompt_mentions_subclause(iss):
    """Prompt mentions the target subclause."""
    assert "§6.3" in iss.build_prompt("6.3", "~/LRM.pdf")


def test_build_prompt_mentions_read_only(iss):
    """Prompt explicitly states the oracle is read-only."""
    assert "READ-ONLY" in iss.build_prompt("6.3", "~/LRM.pdf")


def test_build_prompt_mentions_lrm(iss):
    """Prompt embeds the LRM path."""
    assert "~/LRM.pdf" in iss.build_prompt("6.3", "~/LRM.pdf")


def test_build_prompt_includes_canonical_files(iss):
    """Prompt lists at least one canonical test file for the subclause."""
    prompt = iss.build_prompt("6.3", "~/LRM.pdf")
    assert "test_parser_clause_06_03.cpp" in prompt


def test_build_prompt_lists_all_five_conditions(iss):
    """Prompt names all five satisfaction conditions."""
    prompt = iss.build_prompt("6.3", "~/LRM.pdf")
    missing = [c for c in SATISFACTION_CONDITIONS if c not in prompt]
    assert missing == []


def test_build_prompt_requests_json_output(iss):
    """Prompt instructs the oracle to output a single JSON object."""
    assert "JSON object" in iss.build_prompt("6.3", "~/LRM.pdf")


def test_build_prompt_describes_rollup_for_parents(iss):
    """Prompt explains that parent subclauses roll up over children."""
    assert "rolls up" in iss.build_prompt("33.4", "~/LRM.pdf")


def test_build_prompt_forbids_self_recursion(iss):
    """Prompt forbids the oracle from invoking itself recursively."""
    assert "recursively" in iss.build_prompt("33.4", "~/LRM.pdf")


def test_build_prompt_includes_pascalcase_naming(iss):
    """Prompt mentions the PascalCase naming convention."""
    assert "PascalCase" in iss.build_prompt("6.3", "~/LRM.pdf")


# ---- extract_json_object ----------------------------------------------------


def test_extract_json_object_bare(iss):
    """A bare JSON object is returned verbatim."""
    assert iss.extract_json_object('{"a": 1}') == '{"a": 1}'


def test_extract_json_object_with_surrounding_text(iss):
    """A JSON object surrounded by text is extracted."""
    assert iss.extract_json_object('preamble {"a": 1} trailer') == '{"a": 1}'


def test_extract_json_object_fenced(iss):
    """A JSON object inside a ```json``` fence is extracted."""
    text = '```json\n{"a": 1}\n```'
    assert iss.extract_json_object(text) == '{"a": 1}'


def test_extract_json_object_fenced_no_lang(iss):
    """A JSON object inside an unmarked code fence is extracted."""
    text = '```\n{"a": 1}\n```'
    assert iss.extract_json_object(text) == '{"a": 1}'


def test_extract_json_object_raises_when_missing(iss):
    """Text without any JSON object raises ValueError."""
    with pytest.raises(ValueError):
        iss.extract_json_object("no json here")


# ---- parse_diagnostic -------------------------------------------------------


def test_parse_diagnostic_all_satisfied(iss):
    """All-satisfied JSON parses into a satisfied diagnostic."""
    diag = iss.parse_diagnostic(json.dumps(_all_satisfied_payload()))
    assert diag.verdict == "yes"


def test_parse_diagnostic_with_failures(iss):
    """A failure list parses through to the diagnostic verbatim."""
    payload = _all_satisfied_payload()
    payload["rule_coverage"] = ["rule 7 has no production code"]
    diag = iss.parse_diagnostic(json.dumps(payload))
    assert diag.rule_coverage == ["rule 7 has no production code"]


def test_parse_diagnostic_with_failures_verdict_no(iss):
    """A diagnostic with any failure has verdict 'no'."""
    payload = _all_satisfied_payload()
    payload["test_coverage"] = ["rule 9 has no test"]
    diag = iss.parse_diagnostic(json.dumps(payload))
    assert diag.verdict == "no"


def test_parse_diagnostic_handles_fenced_json(iss):
    """A fenced JSON oracle response parses."""
    text = "```json\n" + json.dumps(_all_satisfied_payload()) + "\n```"
    diag = iss.parse_diagnostic(text)
    assert diag.verdict == "yes"


def test_parse_diagnostic_rejects_missing_condition(iss):
    """An object missing one of the five conditions raises ValueError."""
    payload = _all_satisfied_payload()
    del payload["naming"]
    with pytest.raises(ValueError):
        iss.parse_diagnostic(json.dumps(payload))


def test_parse_diagnostic_rejects_empty_failure_list(iss):
    """An empty list for a condition is invalid (must be a literal SATISFIED)."""
    payload = _all_satisfied_payload()
    payload["rule_coverage"] = []
    with pytest.raises(ValueError):
        iss.parse_diagnostic(json.dumps(payload))


def test_parse_diagnostic_rejects_non_string_list_items(iss):
    """A failure list of non-strings raises ValueError."""
    payload = _all_satisfied_payload()
    payload["rule_coverage"] = [42]
    with pytest.raises(ValueError):
        iss.parse_diagnostic(json.dumps(payload))


def test_parse_diagnostic_rejects_unknown_value(iss):
    """A non-list, non-'satisfied' value raises ValueError."""
    payload = _all_satisfied_payload()
    payload["naming"] = "maybe"
    with pytest.raises(ValueError):
        iss.parse_diagnostic(json.dumps(payload))


# ---- diagnostic_to_payload --------------------------------------------------


def _full_diagnostic():
    """Return a SubclauseDiagnostic with one failure and four satisfied."""
    return SubclauseDiagnostic(
        rule_coverage=["rule 7 has no production code"],
        test_coverage=SATISFIED,
        test_placement=SATISFIED,
        naming=SATISFIED,
        deduplication=SATISFIED,
    )


def test_diagnostic_to_payload_includes_verdict(iss):
    """The serialised payload includes the rolled-up verdict field."""
    payload = iss.diagnostic_to_payload(_full_diagnostic())
    assert payload["verdict"] == "no"


def test_diagnostic_to_payload_preserves_failures(iss):
    """The serialised payload preserves failure lists verbatim."""
    payload = iss.diagnostic_to_payload(_full_diagnostic())
    assert payload["rule_coverage"] == ["rule 7 has no production code"]


def test_diagnostic_to_payload_preserves_satisfied(iss):
    """The serialised payload preserves satisfied conditions verbatim."""
    payload = iss.diagnostic_to_payload(_full_diagnostic())
    assert payload["test_coverage"] == SATISFIED


# ---- run_oracle -------------------------------------------------------------


def _patched_run(stdout, *, returncode=0, stderr=""):
    """Patch subprocess.run with a stubbed CompletedProcess."""
    completed = _claude_completed(stdout, returncode=returncode, stderr=stderr)
    return patch(
        "is_subclause_satisfied.subprocess.run",
        return_value=completed,
    )


def test_run_oracle_returns_result_text(iss):
    """run_oracle returns the .result string from the Claude CLI payload."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout):
        text = iss.run_oracle("prompt", model="opus")
    assert text == json.dumps(_all_satisfied_payload())


def test_run_oracle_passes_model_to_cli(iss):
    """run_oracle passes the model argument to the Claude CLI."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("prompt", model="haiku")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_oracle_passes_disallowed_tools(iss):
    """run_oracle passes --disallowedTools to the Claude CLI."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("prompt", model="opus")
    assert "--disallowedTools" in mock_run.call_args[0][0]


def test_run_oracle_disallowed_tools_blocks_write(iss):
    """run_oracle's disallowedTools value blocks the Write tool."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("prompt", model="opus")
    cmd = mock_run.call_args[0][0]
    assert "Write" in cmd[cmd.index("--disallowedTools") + 1]


def test_run_oracle_disallowed_tools_blocks_edit(iss):
    """run_oracle's disallowedTools value blocks the Edit tool."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("prompt", model="opus")
    cmd = mock_run.call_args[0][0]
    assert "Edit" in cmd[cmd.index("--disallowedTools") + 1]


def test_run_oracle_uses_dangerously_skip_permissions(iss):
    """run_oracle invokes the Claude CLI with --dangerously-skip-permissions."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("prompt", model="opus")
    assert "--dangerously-skip-permissions" in mock_run.call_args[0][0]


def test_run_oracle_writes_prompt_to_stdin(iss):
    """run_oracle passes the prompt to subprocess.run as input."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("hello prompt", model="opus")
    assert mock_run.call_args[1]["input"] == "hello prompt"


def test_run_oracle_uses_json_output_format(iss):
    """run_oracle requests --output-format json from the Claude CLI."""
    stdout = _claude_response(_all_satisfied_payload())
    with _patched_run(stdout) as mock_run:
        iss.run_oracle("prompt", model="opus")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--output-format") + 1] == "json"


def test_run_oracle_env_drops_claudecode(iss):
    """run_oracle's env passed to subprocess.run has no CLAUDECODE."""
    stdout = _claude_response(_all_satisfied_payload())
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        with _patched_run(stdout) as mock_run:
            iss.run_oracle("prompt", model="opus")
    assert "CLAUDECODE" not in mock_run.call_args[1]["env"]


def test_run_oracle_env_preserves_other_vars(iss):
    """run_oracle's env passed to subprocess.run preserves other vars."""
    stdout = _claude_response(_all_satisfied_payload())
    with patch.dict("os.environ", {"SOME_VAR": "value"}, clear=False):
        with _patched_run(stdout) as mock_run:
            iss.run_oracle("prompt", model="opus")
    assert mock_run.call_args[1]["env"].get("SOME_VAR") == "value"


def test_run_oracle_exits_on_nonzero(iss):
    """A non-zero exit code is loud-fatal."""
    with _patched_run("", returncode=1, stderr="boom"):
        with pytest.raises(SystemExit):
            iss.run_oracle("prompt", model="opus")


def test_run_oracle_dumps_stderr_on_nonzero(iss, capsys):
    """Non-zero exit dumps stderr to the terminal."""
    with _patched_run("", returncode=1, stderr="UNIQUE_STDERR"):
        try:
            iss.run_oracle("prompt", model="opus")
        except SystemExit:
            pass
    assert "UNIQUE_STDERR" in capsys.readouterr().err


def test_run_oracle_exits_on_non_json_stdout(iss):
    """Non-JSON stdout from the Claude CLI is loud-fatal."""
    with _patched_run("not json"):
        with pytest.raises(SystemExit):
            iss.run_oracle("prompt", model="opus")


def test_run_oracle_dumps_non_json_stdout(iss, capsys):
    """Non-JSON stdout is echoed to stderr."""
    with _patched_run("WEIRD_BAD_JSON"):
        try:
            iss.run_oracle("prompt", model="opus")
        except SystemExit:
            pass
    assert "WEIRD_BAD_JSON" in capsys.readouterr().err


def test_run_oracle_exits_when_result_missing(iss):
    """Claude payload without a .result field is loud-fatal."""
    with _patched_run(json.dumps({"other": "value"})):
        with pytest.raises(SystemExit):
            iss.run_oracle("prompt", model="opus")


def test_run_oracle_exits_when_result_empty(iss):
    """Claude payload with empty .result is loud-fatal."""
    with _patched_run(json.dumps({"result": ""})):
        with pytest.raises(SystemExit):
            iss.run_oracle("prompt", model="opus")


def test_run_oracle_exits_when_result_non_string(iss):
    """Claude payload with non-string .result is loud-fatal."""
    with _patched_run(json.dumps({"result": 42})):
        with pytest.raises(SystemExit):
            iss.run_oracle("prompt", model="opus")


# ---- main -------------------------------------------------------------------


def _run_main(iss, tmp_path, *, payload=None, extra=None):
    """Run main() with run_oracle stubbed; return captured stdout."""
    payload = payload or _all_satisfied_payload()
    args = _args_with_lrm(tmp_path, *(extra or []))
    with patch(
        "is_subclause_satisfied.run_oracle",
        return_value=json.dumps(payload),
    ) as mock_run:
        iss.main(args)
    return mock_run


def test_main_invokes_run_oracle(iss, tmp_path):
    """main() invokes run_oracle exactly once."""
    mock_run = _run_main(iss, tmp_path)
    assert mock_run.call_count == 1


def test_main_passes_model_to_run_oracle(iss, tmp_path):
    """main() forwards --model to run_oracle."""
    mock_run = _run_main(iss, tmp_path, extra=["--model", "haiku"])
    assert mock_run.call_args[1]["model"] == "haiku"


def test_main_prints_diagnostic_json(iss, tmp_path, capsys):
    """main() prints the diagnostic JSON to stdout."""
    _run_main(iss, tmp_path)
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "yes"


def test_main_prints_all_conditions(iss, tmp_path, capsys):
    """main() includes every condition in the printed JSON."""
    _run_main(iss, tmp_path)
    payload = json.loads(capsys.readouterr().out)
    missing = [c for c in SATISFACTION_CONDITIONS if c not in payload]
    assert missing == []


def test_main_prints_failure_verdict_no(iss, tmp_path, capsys):
    """main() reports verdict 'no' when the oracle returns failures."""
    bad = _all_satisfied_payload()
    bad["test_coverage"] = ["rule 9 has no test"]
    _run_main(iss, tmp_path, payload=bad)
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "no"


def test_main_logs_subclause_to_stderr(iss, tmp_path, capsys):
    """main() prints a one-line oracle banner to stderr."""
    _run_main(iss, tmp_path)
    assert "§4.1" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("is_subclause_satisfied", run_name="__main__")
