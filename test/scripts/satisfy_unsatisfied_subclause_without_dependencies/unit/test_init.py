"""Unit tests for satisfy_unsatisfied_subclause_without_dependencies."""

import runpy
from unittest.mock import patch

import pytest

from lib.python.satisfy import SATISFACTION_CONDITIONS
from lib.python.satisfy.mutator import load_diagnostic
from lib.python.test_fixtures.satisfy import (
    all_satisfied_payload,
    failing_payload,
    make_lrm,
    write_diagnostic,
)


# ---- helpers ----------------------------------------------------------------


def _args(tmp_path, payload, **overrides):
    """Build a CLI argv pointing --diagnostic-file at *payload*."""
    return [
        "--lrm", overrides.get("lrm", str(make_lrm(tmp_path))),
        "--subclause", overrides.get("subclause", "33.4.1.5"),
        "--diagnostic-file", str(write_diagnostic(tmp_path, payload)),
        "--issue", str(overrides.get("issue", 42)),
        "--model", overrides.get("model", "opus"),
    ]


def _all_satisfied():
    """Return a satisfied payload."""
    return all_satisfied_payload()


def _failing_payload():
    """Return a payload with a single rule_coverage failure."""
    return failing_payload(
        "rule_coverage", failures=["rule 7 has no production code"],
    )


# ---- build_prompt ----------------------------------------------------------


def _build_prompt_with_failing(sus, tmp_path):
    """Build the prompt with a single rule_coverage failure."""
    diag = load_diagnostic(write_diagnostic(tmp_path, _failing_payload()))
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
    assert (
        "no remaining dependencies"
        in _build_prompt_with_failing(sus, tmp_path)
    )


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
            "--lrm", str(make_lrm(tmp_path)),
            "--diagnostic-file", str(write_diagnostic(tmp_path, _all_satisfied())),
            "--issue", "1",
        ])


def test_main_requires_diagnostic_file(sus, tmp_path):
    """main() exits when --diagnostic-file is missing."""
    with pytest.raises(SystemExit):
        sus.main([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclause", "4.1",
            "--issue", "1",
        ])


def test_main_requires_issue(sus, tmp_path):
    """main() exits when --issue is missing."""
    with pytest.raises(SystemExit):
        sus.main([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclause", "4.1",
            "--diagnostic-file", str(write_diagnostic(tmp_path, _all_satisfied())),
        ])


def test_main_rejects_bad_clause(sus, tmp_path):
    """main() exits when --subclause is not a valid clause string."""
    with pytest.raises(SystemExit):
        sus.main(_args(tmp_path, _all_satisfied(), subclause="bad"))


# ---- main: behaviour --------------------------------------------------------


def _patched_runner():
    """Patch run_single_subclause_mutator for main() runs."""
    return patch(
        "satisfy_unsatisfied_subclause_without_dependencies"
        ".run_single_subclause_mutator",
    )


def test_main_skips_when_diagnostic_already_satisfied(sus, tmp_path, capsys):
    """main() prints a 'nothing to do' message when verdict is yes."""
    with _patched_runner() as runner:
        sus.main(_args(tmp_path, _all_satisfied()))
    err = capsys.readouterr().err
    assert "nothing to do" in err and not runner.called


def test_main_invokes_mutator_when_diagnostic_failing(sus, tmp_path):
    """main() invokes the shared mutator runner when the diagnostic fails."""
    with _patched_runner() as runner:
        sus.main(_args(tmp_path, _failing_payload()))
    assert runner.called


def test_main_passes_args_namespace_to_runner(sus, tmp_path):
    """main() forwards the parsed argparse namespace to the runner."""
    with _patched_runner() as runner:
        sus.main(_args(tmp_path, _failing_payload(), model="haiku"))
    assert runner.call_args[0][0].model == "haiku"


def test_main_passes_prompt_to_runner(sus, tmp_path):
    """main() supplies a prompt that names the target subclause."""
    with _patched_runner() as runner:
        sus.main(_args(tmp_path, _failing_payload()))
    prompt = runner.call_args[0][1]
    assert "§33.4.1.5" in prompt


def test_main_logs_subclause_to_stderr(sus, tmp_path, capsys):
    """main() prints a one-line mutator banner to stderr."""
    with _patched_runner():
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
