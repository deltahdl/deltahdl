"""Unit tests for is_subclause_satisfied (oracle script)."""

import json
import runpy
from unittest.mock import patch

import pytest

from lib.python.satisfy import (
    SATISFACTION_CONDITIONS,
    SATISFIED,
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


# ---- main argument plumbing ------------------------------------------------


def test_main_requires_subclause(iss, tmp_path):
    """main() exits when --subclause is missing."""
    with pytest.raises(SystemExit):
        iss.main(["--lrm", str(_make_lrm(tmp_path))])


def test_main_requires_lrm(iss):
    """main() exits when --lrm is missing."""
    with pytest.raises(SystemExit):
        iss.main(["--subclause", "4.1"])


def test_main_rejects_bad_clause(iss, tmp_path):
    """main() exits when --subclause is not a valid clause string."""
    with pytest.raises(SystemExit):
        iss.main([
            "--lrm", str(_make_lrm(tmp_path)), "--subclause", "bad",
        ])


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


def _full_diagnostic(iss):
    """Return a parsed diagnostic with one failure and four satisfied."""
    payload = _all_satisfied_payload()
    payload["rule_coverage"] = ["rule 7 has no production code"]
    return iss.parse_diagnostic(json.dumps(payload))


def test_diagnostic_to_payload_includes_verdict(iss):
    """The serialised payload includes the rolled-up verdict field."""
    payload = iss.diagnostic_to_payload(_full_diagnostic(iss))
    assert payload["verdict"] == "no"


def test_diagnostic_to_payload_preserves_failures(iss):
    """The serialised payload preserves failure lists verbatim."""
    payload = iss.diagnostic_to_payload(_full_diagnostic(iss))
    assert payload["rule_coverage"] == ["rule 7 has no production code"]


def test_diagnostic_to_payload_preserves_satisfied(iss):
    """The serialised payload preserves satisfied conditions verbatim."""
    payload = iss.diagnostic_to_payload(_full_diagnostic(iss))
    assert payload["test_coverage"] == SATISFIED


# ---- main -------------------------------------------------------------------


def _run_main(iss, tmp_path, *, payload=None, extra=None):
    """Run main() with run_oracle_call stubbed; return captured mock."""
    payload = payload or _all_satisfied_payload()
    args = _args_with_lrm(tmp_path, *(extra or []))
    with patch(
        "is_subclause_satisfied.run_oracle_call",
        return_value=json.dumps(payload),
    ) as mock_run:
        iss.main(args)
    return mock_run


def test_main_invokes_run_oracle(iss, tmp_path):
    """main() invokes the oracle Claude call exactly once."""
    mock_run = _run_main(iss, tmp_path)
    assert mock_run.call_count == 1


def test_main_passes_model_to_run_oracle(iss, tmp_path):
    """main() forwards --model to the oracle Claude call."""
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
    """main() prints a one-line satisfaction-oracle banner to stderr."""
    _run_main(iss, tmp_path)
    assert "§4.1" in capsys.readouterr().err


def test_main_banner_identifies_satisfaction_oracle(iss, tmp_path, capsys):
    """main() banner identifies the satisfaction oracle (not dependency)."""
    _run_main(iss, tmp_path)
    assert "Satisfaction" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("is_subclause_satisfied", run_name="__main__")
