"""Unit tests for satisfy_unsatisfied_subclause_with_satisfied_dependencies."""

import runpy
from unittest.mock import patch

import pytest

from lib.python.satisfy.mutator import load_diagnostic
from lib.python.test_fixtures.satisfy import (
    all_satisfied_payload,
    failing_payload,
    make_lrm,
    write_diagnostic,
)


# ---- helpers ----------------------------------------------------------------


def _args(tmp_path, payload, deps="33.6.1,33.4.1.5", **overrides):
    """Build a CLI argv pointing --diagnostic-file at *payload*."""
    return [
        "--lrm", overrides.get("lrm", str(make_lrm(tmp_path))),
        "--subclause", overrides.get("subclause", "33.4"),
        "--diagnostic-file", str(write_diagnostic(tmp_path, payload)),
        "--issue", str(overrides.get("issue", 42)),
        "--model", overrides.get("model", "opus"),
        "--satisfied-dependencies", deps,
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


def _build_prompt_with_failing(swd, tmp_path, deps=None):
    """Return the failing-diagnostic prompt with optional deps list."""
    diag = load_diagnostic(write_diagnostic(tmp_path, _failing_payload()))
    return swd.build_prompt(
        "33.4", "~/LRM.pdf", diag, deps if deps is not None else [],
    )


def test_build_prompt_mentions_subclause(swd, tmp_path):
    """Prompt mentions the target subclause."""
    assert "§33.4" in _build_prompt_with_failing(swd, tmp_path)


def test_build_prompt_includes_diagnostic_failures(swd, tmp_path):
    """Prompt embeds the diagnostic failure descriptions."""
    assert (
        "rule 7 has no production code"
        in _build_prompt_with_failing(swd, tmp_path)
    )


def test_build_prompt_lists_satisfied_deps(swd, tmp_path):
    """Prompt lists the dependencies that are already satisfied."""
    prompt = _build_prompt_with_failing(swd, tmp_path, ["33.6.1", "33.4.1.5"])
    assert "§33.6.1" in prompt and "§33.4.1.5" in prompt


def test_build_prompt_describes_dep_reuse(swd, tmp_path):
    """Prompt explains that satisfied deps may be referenced freely."""
    prompt = _build_prompt_with_failing(swd, tmp_path, ["33.6.1"])
    assert "reference their machinery" in prompt


def test_build_prompt_handles_empty_deps(swd, tmp_path):
    """Prompt handles the empty dependency list with a no-deps note."""
    prompt = _build_prompt_with_failing(swd, tmp_path, [])
    assert "No external dependencies" in prompt


def test_build_prompt_forbids_git(swd, tmp_path):
    """Prompt explicitly forbids running git."""
    assert "git" in _build_prompt_with_failing(swd, tmp_path)


# ---- main: argument validation --------------------------------------------


def test_main_requires_diagnostic_file(swd, tmp_path):
    """main() exits when --diagnostic-file is missing."""
    with pytest.raises(SystemExit):
        swd.main([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclause", "33.4",
            "--issue", "1",
        ])


def test_main_accepts_empty_dependencies(swd, tmp_path):
    """main() accepts an empty --satisfied-dependencies value."""
    with _patched_runner():
        swd.main(_args(tmp_path, _failing_payload(), deps=""))


def test_main_rejects_bad_clause(swd, tmp_path):
    """main() exits when --subclause is not a valid clause string."""
    with pytest.raises(SystemExit):
        swd.main(_args(tmp_path, _all_satisfied(), subclause="bad"))


# ---- main: behaviour --------------------------------------------------------


def _patched_runner():
    """Patch run_single_subclause_mutator for main() runs."""
    return patch(
        "satisfy_unsatisfied_subclause_with_satisfied_dependencies"
        ".run_single_subclause_mutator",
    )


def test_main_skips_when_diagnostic_already_satisfied(swd, tmp_path, capsys):
    """main() prints a 'nothing to do' message when verdict is yes."""
    with _patched_runner() as runner:
        swd.main(_args(tmp_path, _all_satisfied()))
    assert "nothing to do" in capsys.readouterr().err and not runner.called


def test_main_invokes_mutator_when_failing(swd, tmp_path):
    """main() invokes the shared mutator runner when the diagnostic fails."""
    with _patched_runner() as runner:
        swd.main(_args(tmp_path, _failing_payload()))
    assert runner.called


def test_main_passes_deps_into_prompt(swd, tmp_path):
    """main() forwards the parsed dependencies into the Claude prompt."""
    with _patched_runner() as runner:
        swd.main(_args(tmp_path, _failing_payload(), deps="33.6.1"))
    prompt = runner.call_args[0][1]
    assert "§33.6.1" in prompt


def test_main_logs_subclause_to_stderr(swd, tmp_path, capsys):
    """main() prints a one-line mutator banner to stderr."""
    with _patched_runner():
        swd.main(_args(tmp_path, _failing_payload()))
    assert "§33.4" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module(
            "satisfy_unsatisfied_subclause_with_satisfied_dependencies",
            run_name="__main__",
        )
