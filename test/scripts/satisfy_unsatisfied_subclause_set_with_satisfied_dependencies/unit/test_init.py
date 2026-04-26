"""Unit tests for the cycle-set mutator script."""

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


def _two_member_args(tmp_path, payloads, **overrides):
    """Build a CLI argv for a two-member cycle."""
    diag_a = write_diagnostic(tmp_path, payloads[0], name="a.json")
    diag_b = write_diagnostic(tmp_path, payloads[1], name="b.json")
    return [
        "--lrm", overrides.get("lrm", str(make_lrm(tmp_path))),
        "--subclauses", overrides.get(
            "subclauses", "33.4.1.5,33.4.1.6",
        ),
        "--diagnostic-files", f"{diag_a},{diag_b}",
        "--issues", overrides.get("issues", "10,11"),
        "--model", overrides.get("model", "opus"),
        "--satisfied-dependencies", overrides.get(
            "satisfied_deps", "33.6.1",
        ),
    ]


def _failing():
    """Return a payload with a single rule_coverage failure."""
    return failing_payload(
        "rule_coverage", failures=["needs cycle peer machinery"],
    )


# ---- parse_args -------------------------------------------------------------


def test_parse_args_accepts_two_members(sset, tmp_path):
    """A two-member cycle is accepted."""
    args = sset.parse_args(_two_member_args(
        tmp_path, [_failing(), _failing()],
    ))
    assert args.subclauses == ["33.4.1.5", "33.4.1.6"]


def test_parse_args_parses_issues_as_ints(sset, tmp_path):
    """--issues parses to a list of ints."""
    args = sset.parse_args(_two_member_args(
        tmp_path, [_failing(), _failing()],
    ))
    assert args.issues == [10, 11]


def test_parse_args_rejects_single_member(sset, tmp_path):
    """A one-member 'cycle' is rejected (caller should use the singular)."""
    diag = write_diagnostic(tmp_path, _failing(), name="a.json")
    with pytest.raises(SystemExit):
        sset.parse_args([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclauses", "33.4.1.5",
            "--diagnostic-files", str(diag),
            "--issues", "10",
        ])


def test_parse_args_rejects_four_members(sset, tmp_path):
    """A four-member cycle exceeds the cap and is rejected."""
    diags = [
        write_diagnostic(tmp_path, _failing(), name=f"{i}.json")
        for i in range(4)
    ]
    with pytest.raises(SystemExit):
        sset.parse_args([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclauses", "1.1,1.2,1.3,1.4",
            "--diagnostic-files", ",".join(str(p) for p in diags),
            "--issues", "1,2,3,4",
        ])


def test_parse_args_rejects_mismatched_lengths(sset, tmp_path):
    """Mismatched --diagnostic-files and --subclauses are rejected."""
    diag = write_diagnostic(tmp_path, _failing(), name="a.json")
    with pytest.raises(SystemExit):
        sset.parse_args([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclauses", "1.1,1.2",
            "--diagnostic-files", str(diag),
            "--issues", "1,2",
        ])


def test_parse_args_rejects_mismatched_issues(sset, tmp_path):
    """Mismatched --issues length is rejected."""
    diags = [
        write_diagnostic(tmp_path, _failing(), name=f"{i}.json")
        for i in range(2)
    ]
    with pytest.raises(SystemExit):
        sset.parse_args([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclauses", "1.1,1.2",
            "--diagnostic-files", ",".join(str(p) for p in diags),
            "--issues", "1",
        ])


# ---- build_prompt -----------------------------------------------------------


def _build_two_member_prompt(sset, tmp_path, deps=None):
    """Build a two-member cycle prompt for assertion."""
    diag_a = load_diagnostic(
        write_diagnostic(tmp_path, _failing(), name="a.json"),
    )
    diag_b = load_diagnostic(
        write_diagnostic(tmp_path, _failing(), name="b.json"),
    )
    return sset.build_prompt(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf",
        [diag_a, diag_b], deps if deps is not None else [],
    )


def test_build_prompt_lists_each_cycle_member(sset, tmp_path):
    """Prompt names each cycle member with the section sign."""
    prompt = _build_two_member_prompt(sset, tmp_path)
    assert "§33.4.1.5" in prompt and "§33.4.1.6" in prompt


def test_build_prompt_describes_cycle_relationship(sset, tmp_path):
    """Prompt explains that cycle members must be implemented together."""
    assert "implemented together" in _build_two_member_prompt(sset, tmp_path)


def test_build_prompt_lists_each_diagnostic(sset, tmp_path):
    """Prompt embeds a DIAGNOSTIC section per cycle member."""
    prompt = _build_two_member_prompt(sset, tmp_path)
    assert prompt.count("DIAGNOSTIC for") == 2


def test_build_prompt_includes_failure(sset, tmp_path):
    """Prompt includes each member's failure descriptions."""
    prompt = _build_two_member_prompt(sset, tmp_path)
    assert "needs cycle peer machinery" in prompt


def test_build_prompt_lists_external_deps(sset, tmp_path):
    """Prompt lists the external dependencies that are already satisfied."""
    prompt = _build_two_member_prompt(sset, tmp_path, ["33.6.1"])
    assert "§33.6.1" in prompt


def test_build_prompt_handles_no_external_deps(sset, tmp_path):
    """Prompt handles the no-external-deps case with a notice."""
    prompt = _build_two_member_prompt(sset, tmp_path, [])
    assert "No external dependencies" in prompt


def test_build_prompt_forbids_git(sset, tmp_path):
    """Prompt explicitly forbids running git."""
    assert "git" in _build_two_member_prompt(sset, tmp_path)


# ---- main ------------------------------------------------------------------


def _patched():
    """Patch the Claude call and the commit step."""
    return (
        patch(
            "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies"
            ".run_mutator_call",
        ),
        patch(
            "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies"
            ".commit_mutator_result",
            return_value=True,
        ),
    )


def test_main_skips_when_all_members_satisfied(sset, tmp_path, capsys):
    """main() exits silently when every member is already satisfied."""
    payloads = [all_satisfied_payload(), all_satisfied_payload()]
    mock_run, mock_commit = _patched()
    with mock_run as call:
        with mock_commit:
            sset.main(_two_member_args(tmp_path, payloads))
    assert "nothing to do" in capsys.readouterr().err and not call.called


def test_main_invokes_mutator_when_any_member_fails(sset, tmp_path):
    """main() invokes the Claude mutator when any member is failing."""
    payloads = [_failing(), all_satisfied_payload()]
    mock_run, mock_commit = _patched()
    with mock_run as call:
        with mock_commit:
            sset.main(_two_member_args(tmp_path, payloads))
    assert call.called


def test_main_commits_with_all_issues(sset, tmp_path):
    """main() commits with one Closes trailer per cycle member."""
    payloads = [_failing(), _failing()]
    mock_run, mock_commit = _patched()
    with mock_run:
        with mock_commit as commit:
            sset.main(_two_member_args(tmp_path, payloads))
    assert commit.call_args[0] == (["33.4.1.5", "33.4.1.6"], [10, 11])


def test_main_warns_when_no_changes(sset, tmp_path, capsys):
    """main() warns when the cycle mutator made no source-tree changes."""
    payloads = [_failing(), _failing()]
    mock_run = patch(
        "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies"
        ".run_mutator_call",
    )
    mock_commit = patch(
        "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies"
        ".commit_mutator_result",
        return_value=False,
    )
    with mock_run:
        with mock_commit:
            sset.main(_two_member_args(tmp_path, payloads))
    assert "produced no source" in capsys.readouterr().err


def test_main_logs_subclauses_to_stderr(sset, tmp_path, capsys):
    """main() prints a one-line cycle banner to stderr."""
    payloads = [_failing(), _failing()]
    mock_run, mock_commit = _patched()
    with mock_run:
        with mock_commit:
            sset.main(_two_member_args(tmp_path, payloads))
    err = capsys.readouterr().err
    assert "33.4.1.5" in err and "33.4.1.6" in err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module(
            "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies",
            run_name="__main__",
        )
