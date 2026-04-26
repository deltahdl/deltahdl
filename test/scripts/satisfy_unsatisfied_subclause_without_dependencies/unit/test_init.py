"""Unit tests for satisfy_unsatisfied_subclause_without_dependencies."""

import json
import runpy
from unittest.mock import patch

import pytest

from lib.python.satisfy import SATISFACTION_CONDITIONS, SATISFIED
from lib.python.satisfy.mutator import load_diagnostic


# ---- helpers ----------------------------------------------------------------


def _make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


def _write_diag(tmp_path, payload):
    """Write a diagnostic JSON file and return the path."""
    path = tmp_path / "diag.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def _all_satisfied():
    """Return a payload with all five conditions satisfied."""
    return {c: SATISFIED for c in SATISFACTION_CONDITIONS}


def _failing_payload():
    """Return a payload with one rule_coverage failure."""
    payload = _all_satisfied()
    payload["rule_coverage"] = ["rule 7 has no production code"]
    return payload


def _args(tmp_path, payload, **overrides):
    """Build a CLI argv pointing --diagnostic-file at *payload*."""
    return [
        "--lrm", overrides.get("lrm", str(_make_lrm(tmp_path))),
        "--subclause", overrides.get("subclause", "33.4.1.5"),
        "--diagnostic-file", str(_write_diag(tmp_path, payload)),
        "--issue", str(overrides.get("issue", 42)),
        "--model", overrides.get("model", "opus"),
    ]


# ---- build_prompt ----------------------------------------------------------


def _build_prompt_with_failing(sus, tmp_path):
    """Build the prompt with a single rule_coverage failure."""
    diag = load_diagnostic(_write_diag(tmp_path, _failing_payload()))
    return sus.build_prompt("33.4.1.5", "~/LRM.pdf", diag)


def test_build_prompt_mentions_subclause(sus, tmp_path):
    """Prompt mentions the target subclause."""
    assert "§33.4.1.5" in _build_prompt_with_failing(sus, tmp_path)


def test_build_prompt_includes_diagnostic_failures(sus, tmp_path):
    """Prompt embeds the diagnostic failure descriptions."""
    assert (
        "rule 7 has no production code"
        in _build_prompt_with_failing(sus, tmp_path)
    )


def test_build_prompt_says_no_dependencies(sus, tmp_path):
    """Prompt asserts the subclause has no remaining dependencies."""
    assert "no dependencies" in _build_prompt_with_failing(sus, tmp_path)


def test_build_prompt_forbids_git(sus, tmp_path):
    """Prompt explicitly forbids running git."""
    assert "git" in _build_prompt_with_failing(sus, tmp_path)


def test_build_prompt_describes_each_failure_kind(sus, tmp_path):
    """Prompt names instructions for each of the five failure kinds."""
    prompt = _build_prompt_with_failing(sus, tmp_path)
    missing = [c for c in SATISFACTION_CONDITIONS if c not in prompt]
    assert missing == []


def test_build_prompt_mentions_lrm(sus, tmp_path):
    """Prompt embeds the LRM path."""
    assert "~/LRM.pdf" in _build_prompt_with_failing(sus, tmp_path)


# ---- main: argument validation --------------------------------------------


def test_main_requires_subclause(sus, tmp_path):
    """main() exits when --subclause is missing."""
    with pytest.raises(SystemExit):
        sus.main([
            "--lrm", str(_make_lrm(tmp_path)),
            "--diagnostic-file", str(_write_diag(tmp_path, _all_satisfied())),
            "--issue", "1",
        ])


def test_main_requires_diagnostic_file(sus, tmp_path):
    """main() exits when --diagnostic-file is missing."""
    with pytest.raises(SystemExit):
        sus.main([
            "--lrm", str(_make_lrm(tmp_path)),
            "--subclause", "4.1",
            "--issue", "1",
        ])


def test_main_requires_issue(sus, tmp_path):
    """main() exits when --issue is missing."""
    with pytest.raises(SystemExit):
        sus.main([
            "--lrm", str(_make_lrm(tmp_path)),
            "--subclause", "4.1",
            "--diagnostic-file", str(_write_diag(tmp_path, _all_satisfied())),
        ])


def test_main_rejects_bad_clause(sus, tmp_path):
    """main() exits when --subclause is not a valid clause string."""
    with pytest.raises(SystemExit):
        sus.main(_args(tmp_path, _all_satisfied(), subclause="bad"))


# ---- main: behaviour --------------------------------------------------------


def _patched_pipeline(*, committed=True):
    """Patch run_mutator_call and commit_mutator_result for main() runs."""
    return (
        patch(
            "satisfy_unsatisfied_subclause_without_dependencies"
            ".run_mutator_call",
        ),
        patch(
            "satisfy_unsatisfied_subclause_without_dependencies"
            ".commit_mutator_result",
            return_value=committed,
        ),
    )


def test_main_skips_when_diagnostic_already_satisfied(sus, tmp_path, capsys):
    """main() prints a 'nothing to do' message when verdict is yes."""
    mock_run, mock_commit = _patched_pipeline()
    with mock_run as call:
        with mock_commit as commit:
            sus.main(_args(tmp_path, _all_satisfied()))
    err = capsys.readouterr().err
    assert ("nothing to do" in err
            and not call.called
            and not commit.called)


def test_main_invokes_mutator_when_diagnostic_failing(sus, tmp_path):
    """main() invokes the Claude mutator call when the diagnostic fails."""
    mock_run, mock_commit = _patched_pipeline()
    with mock_run as call:
        with mock_commit:
            sus.main(_args(tmp_path, _failing_payload()))
    assert call.called


def test_main_passes_model_to_mutator(sus, tmp_path):
    """main() forwards --model to the mutator Claude call."""
    mock_run, mock_commit = _patched_pipeline()
    with mock_run as call:
        with mock_commit:
            sus.main(_args(tmp_path, _failing_payload(), model="haiku"))
    assert call.call_args[1]["model"] == "haiku"


def test_main_calls_commit_with_subclause(sus, tmp_path):
    """main() commits with the target subclause and issue."""
    mock_run, mock_commit = _patched_pipeline()
    with mock_run:
        with mock_commit as commit:
            sus.main(_args(tmp_path, _failing_payload()))
    assert commit.call_args[0] == (["33.4.1.5"], [42])


def test_main_warns_when_no_changes(sus, tmp_path, capsys):
    """main() warns to stderr when the mutator produced no source changes."""
    mock_run, mock_commit = _patched_pipeline(committed=False)
    with mock_run:
        with mock_commit:
            sus.main(_args(tmp_path, _failing_payload()))
    assert "no source-tree changes" in capsys.readouterr().err


def test_main_logs_subclause_to_stderr(sus, tmp_path, capsys):
    """main() prints a one-line mutator banner to stderr."""
    mock_run, mock_commit = _patched_pipeline()
    with mock_run:
        with mock_commit:
            sus.main(_args(tmp_path, _failing_payload()))
    assert "§33.4.1.5" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module(
            "satisfy_unsatisfied_subclause_without_dependencies",
            run_name="__main__",
        )
