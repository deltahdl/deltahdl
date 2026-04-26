"""Unit tests for satisfy_subclause.mutators."""

from unittest.mock import MagicMock, patch

import pytest

from satisfy_subclause.mutators import (
    MUTATOR_DISALLOWED_TOOLS,
    CycleMember,
    build_commit_message,
    build_cycle_prompt,
    build_failure_resolution_block,
    build_no_deps_prompt,
    build_no_external_state_block,
    build_with_deps_prompt,
    commit_mutator_result,
    filter_changes,
    format_diagnostic_summary,
    is_valid_path,
    run_mutator_call,
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_without_dependencies,
    short_circuit_if_satisfied,
)
from satisfy_subclause.oracles import (
    SATISFACTION_CONDITIONS,
    SATISFIED,
    SubclauseDiagnostic,
)


# --- helpers ---------------------------------------------------------------


def _all_satisfied():
    """Return a fully satisfied diagnostic."""
    fields = {c: SATISFIED for c in SATISFACTION_CONDITIONS}
    return SubclauseDiagnostic(**fields)


def _failing_diagnostic():
    """Return a diagnostic with one rule_coverage failure."""
    fields = {c: SATISFIED for c in SATISFACTION_CONDITIONS}
    fields["rule_coverage"] = ["rule 7 has no production code"]
    return SubclauseDiagnostic(**fields)


# --- MUTATOR_DISALLOWED_TOOLS -----------------------------------------------


def test_disallowed_tools_blocks_git() -> None:
    """The mutator disallowed-tools list blocks all git invocations."""
    assert "Bash(git *)" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_gh() -> None:
    """The mutator disallowed-tools list blocks all gh invocations."""
    assert "Bash(gh *)" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pytest() -> None:
    """The mutator disallowed-tools list blocks pytest."""
    assert "Bash(pytest *)" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_cmake() -> None:
    """The mutator disallowed-tools list blocks cmake."""
    assert "Bash(cmake *)" in MUTATOR_DISALLOWED_TOOLS


# --- format_diagnostic_summary ----------------------------------------------


def test_format_diagnostic_summary_all_satisfied() -> None:
    """A fully-satisfied diagnostic formats with five 'satisfied' lines."""
    text = format_diagnostic_summary(_all_satisfied())
    assert text.count("satisfied") == 5


def test_format_diagnostic_summary_lists_failures() -> None:
    """A failure list appears as bullet points under its condition."""
    text = format_diagnostic_summary(_failing_diagnostic())
    assert "rule 7 has no production code" in text


def test_format_diagnostic_summary_names_failing_condition() -> None:
    """The failing condition name appears in the formatted summary."""
    text = format_diagnostic_summary(_failing_diagnostic())
    assert "rule_coverage" in text


# --- run_mutator_call -------------------------------------------------------


def _patched_run(returncode=0):
    """Patch subprocess.run with a CompletedProcess at *returncode*."""
    completed = MagicMock()
    completed.returncode = returncode
    return patch(
        "satisfy_subclause.mutators.subprocess.run",
        return_value=completed,
    )


def test_run_mutator_call_passes_prompt() -> None:
    """run_mutator_call passes the prompt as subprocess input."""
    with _patched_run() as mock_run:
        run_mutator_call("hello prompt", model="opus")
    assert mock_run.call_args[1]["input"] == "hello prompt"


def test_run_mutator_call_passes_model() -> None:
    """run_mutator_call passes --model to the Claude CLI."""
    with _patched_run() as mock_run:
        run_mutator_call("prompt", model="haiku")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_mutator_call_passes_disallowed_tools() -> None:
    """run_mutator_call passes --disallowedTools."""
    with _patched_run() as mock_run:
        run_mutator_call("prompt", model="opus")
    assert "--disallowedTools" in mock_run.call_args[0][0]


def test_run_mutator_call_uses_dangerously_skip_permissions() -> None:
    """run_mutator_call passes --dangerously-skip-permissions."""
    with _patched_run() as mock_run:
        run_mutator_call("prompt", model="opus")
    assert "--dangerously-skip-permissions" in mock_run.call_args[0][0]


def test_run_mutator_call_exits_on_nonzero() -> None:
    """A non-zero exit code is loud-fatal."""
    with _patched_run(returncode=2):
        with pytest.raises(SystemExit):
            run_mutator_call("prompt", model="opus")


def test_run_mutator_call_dumps_message_on_nonzero(capsys) -> None:
    """A non-zero exit prints an error to stderr."""
    with _patched_run(returncode=2):
        try:
            run_mutator_call("prompt", model="opus")
        except SystemExit:
            pass
    assert "code 2" in capsys.readouterr().err


# --- is_valid_path ----------------------------------------------------------


def test_is_valid_path_cpp() -> None:
    """A .cpp file is a valid path."""
    assert is_valid_path("src/foo.cpp") is True


def test_is_valid_path_h() -> None:
    """A .h file is a valid path."""
    assert is_valid_path("src/foo.h") is True


def test_is_valid_path_py() -> None:
    """A .py file is a valid path."""
    assert is_valid_path("scripts/foo.py") is True


def test_is_valid_path_cmakelists() -> None:
    """CMakeLists.txt is a valid path."""
    assert is_valid_path("test/CMakeLists.txt") is True


def test_is_valid_path_garbage() -> None:
    """A garbage entry is rejected."""
    assert is_valid_path("{a,") is False


def test_is_valid_path_no_extension() -> None:
    """A path with no recognised extension is rejected."""
    assert is_valid_path("README") is False


# --- filter_changes ---------------------------------------------------------


def test_filter_changes_keeps_valid() -> None:
    """filter_changes preserves entries with valid extensions."""
    added, _modified, _deleted = filter_changes(
        (["a.cpp", "junk"], [], []),
    )
    assert added == ["a.cpp"]


def test_filter_changes_drops_invalid_modified() -> None:
    """filter_changes drops invalid entries from modified."""
    _added, modified, _deleted = filter_changes(
        ([], ["b.h", "junk"], []),
    )
    assert modified == ["b.h"]


def test_filter_changes_drops_invalid_deleted() -> None:
    """filter_changes drops invalid entries from deleted."""
    _added, _modified, deleted = filter_changes(
        ([], [], ["c.py", "junk"]),
    )
    assert deleted == ["c.py"]


# --- build_commit_message ---------------------------------------------------


def test_build_commit_message_single_subclause_title() -> None:
    """A single-subclause commit title uses 'Satisfy §X' format."""
    msg = build_commit_message(["6.3"], [42], "- Modified foo.cpp")
    assert "Satisfy §6.3" in msg


def test_build_commit_message_set_title() -> None:
    """A multi-subclause commit title names cycle co-implementation."""
    msg = build_commit_message(["33.4.1.5", "33.4.1.6"], [10, 11], "")
    assert "cycle co-implementation" in msg


def test_build_commit_message_includes_summary() -> None:
    """The commit message includes the file-change summary body."""
    msg = build_commit_message(["6.3"], [42], "- Modified foo.cpp")
    assert "- Modified foo.cpp" in msg


def test_build_commit_message_includes_single_closes() -> None:
    """A single-subclause message includes one Closes trailer."""
    msg = build_commit_message(["6.3"], [42], "")
    assert "Closes #42" in msg


def test_build_commit_message_includes_multiple_closes() -> None:
    """A multi-subclause message includes one Closes trailer per issue."""
    msg = build_commit_message(["33.4.1.5", "33.4.1.6"], [10, 11], "")
    assert msg.count("Closes #") == 2


def test_build_commit_message_uses_annex_label() -> None:
    """Annex subclauses appear with their letter prefix (no §)."""
    msg = build_commit_message(["A.7.1"], [42], "")
    assert "Satisfy A.7.1" in msg


# --- commit_mutator_result --------------------------------------------------


def _patched_porcelain(changes):
    """Patch get_porcelain_changes with a fixed return value."""
    return patch(
        "satisfy_subclause.mutators.get_porcelain_changes",
        return_value=changes,
    )


def _patched_commit():
    """Patch commit_and_push with a no-op MagicMock."""
    return patch(
        "satisfy_subclause.mutators.commit_and_push",
        return_value="abc123",
    )


def test_commit_mutator_result_returns_false_when_clean() -> None:
    """commit_mutator_result returns False when the working tree is clean."""
    with _patched_porcelain(([], [], [])), _patched_commit() as mock_c:
        result = commit_mutator_result(["6.3"], [42])
    assert (result, mock_c.called) == (False, False)


def test_commit_mutator_result_returns_true_when_dirty() -> None:
    """commit_mutator_result returns True when porcelain has source files."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit():
        result = commit_mutator_result(["6.3"], [42])
    assert result is True


def test_commit_mutator_result_calls_commit_and_push() -> None:
    """commit_mutator_result invokes commit_and_push with the file list."""
    with _patched_porcelain((["foo.cpp"], ["bar.h"], [])), \
            _patched_commit() as mock_c:
        commit_mutator_result(["6.3"], [42])
    assert mock_c.call_args[0][0] == ["foo.cpp", "bar.h"]


def test_commit_mutator_result_filters_garbage_added() -> None:
    """commit_mutator_result drops garbage paths from added before commit."""
    with _patched_porcelain((["foo.cpp", "{a,"], [], [])), \
            _patched_commit() as mock_c:
        commit_mutator_result(["6.3"], [42])
    assert mock_c.call_args[0][0] == ["foo.cpp"]


def test_commit_mutator_result_filters_garbage_deleted() -> None:
    """commit_mutator_result drops garbage paths from deleted before commit."""
    with _patched_porcelain(([], [], ["foo.cpp", "{a,"])), \
            _patched_commit() as mock_c:
        commit_mutator_result(["6.3"], [42])
    assert mock_c.call_args[0][1] == ["foo.cpp"]


def test_commit_mutator_result_returns_false_when_only_garbage() -> None:
    """commit_mutator_result returns False when porcelain is only garbage."""
    with _patched_porcelain((["{a,"], [], [])), _patched_commit() as mock_c:
        result = commit_mutator_result(["6.3"], [42])
    assert (result, mock_c.called) == (False, False)


# --- shared prompt blocks ----------------------------------------------------


def test_failure_resolution_block_lists_each_condition() -> None:
    """The shared resolution block names every satisfaction condition."""
    text = build_failure_resolution_block()
    missing = [c for c in SATISFACTION_CONDITIONS if c not in text]
    assert missing == []


def test_failure_resolution_block_says_smallest_set() -> None:
    """The shared resolution block requires minimal edits."""
    assert "smallest set of edits" in build_failure_resolution_block()


def test_no_external_state_block_blocks_git() -> None:
    """The no-external-state block forbids git from inside the prompt."""
    assert "git" in build_no_external_state_block()


def test_no_external_state_block_blocks_commit() -> None:
    """The no-external-state block forbids commit/push from inside the prompt."""
    assert "commit or push" in build_no_external_state_block()


# --- short_circuit_if_satisfied --------------------------------------------


def test_short_circuit_returns_true_when_satisfied() -> None:
    """short_circuit_if_satisfied returns True for a satisfied diagnostic."""
    assert short_circuit_if_satisfied("6.3", _all_satisfied()) is True


def test_short_circuit_returns_false_when_failing() -> None:
    """short_circuit_if_satisfied returns False for a failing diagnostic."""
    assert short_circuit_if_satisfied("6.3", _failing_diagnostic()) is False


def test_short_circuit_prints_when_satisfied(capsys) -> None:
    """short_circuit_if_satisfied prints a notice when verdict is yes."""
    short_circuit_if_satisfied("6.3", _all_satisfied())
    assert "nothing to do" in capsys.readouterr().err


def test_short_circuit_silent_when_failing(capsys) -> None:
    """short_circuit_if_satisfied prints nothing when verdict is no."""
    short_circuit_if_satisfied("6.3", _failing_diagnostic())
    assert capsys.readouterr().err == ""


# --- build_no_deps_prompt ---------------------------------------------------


def test_no_deps_prompt_mentions_subclause() -> None:
    """No-deps prompt mentions the target subclause."""
    prompt = build_no_deps_prompt("33.4.1.5", "~/LRM.pdf", _failing_diagnostic())
    assert "§33.4.1.5" in prompt


def test_no_deps_prompt_includes_diagnostic_failures() -> None:
    """No-deps prompt embeds the diagnostic failure descriptions."""
    prompt = build_no_deps_prompt("33.4.1.5", "~/LRM.pdf", _failing_diagnostic())
    assert "rule 7 has no production code" in prompt


def test_no_deps_prompt_says_no_dependencies() -> None:
    """No-deps prompt asserts the subclause has no remaining dependencies."""
    prompt = build_no_deps_prompt("33.4.1.5", "~/LRM.pdf", _failing_diagnostic())
    assert "no remaining dependencies" in prompt


def test_no_deps_prompt_forbids_git() -> None:
    """No-deps prompt explicitly forbids running git."""
    prompt = build_no_deps_prompt("33.4.1.5", "~/LRM.pdf", _failing_diagnostic())
    assert "git" in prompt


def test_no_deps_prompt_describes_each_failure_kind() -> None:
    """No-deps prompt names instructions for each failure kind."""
    prompt = build_no_deps_prompt("33.4.1.5", "~/LRM.pdf", _failing_diagnostic())
    missing = [c for c in SATISFACTION_CONDITIONS if c not in prompt]
    assert missing == []


def test_no_deps_prompt_mentions_lrm() -> None:
    """No-deps prompt embeds the LRM path."""
    prompt = build_no_deps_prompt("33.4.1.5", "~/LRM.pdf", _failing_diagnostic())
    assert "~/LRM.pdf" in prompt


# --- satisfy_unsatisfied_subclause_without_dependencies ---------------------


def _patched_call_and_commit(committed=True):
    """Patch run_mutator_call and commit_mutator_result."""
    return (
        patch("satisfy_subclause.mutators.run_mutator_call"),
        patch(
            "satisfy_subclause.mutators.commit_mutator_result",
            return_value=committed,
        ),
    )


def _target(failing: bool = True, subclause: str = "33.4.1.5",
            issue: int = 42) -> CycleMember:
    """Build a CycleMember target with a satisfied or failing diagnostic."""
    diagnostic = _failing_diagnostic() if failing else _all_satisfied()
    return CycleMember(
        subclause=subclause, diagnostic=diagnostic, issue=issue,
    )


def test_no_deps_skips_when_satisfied() -> None:
    """No-deps mutator is a no-op when the diagnostic is already satisfied."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(failing=False), "~/LRM.pdf", model="opus",
            )
    assert not call.called


def test_no_deps_invokes_mutator_when_failing() -> None:
    """No-deps mutator invokes run_mutator_call when the diagnostic fails."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert call.called


def test_no_deps_passes_model_to_mutator() -> None:
    """No-deps mutator forwards the model arg to run_mutator_call."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="haiku",
            )
    assert call.call_args[1]["model"] == "haiku"


def test_no_deps_commits_with_subclause_and_issue() -> None:
    """No-deps mutator commits with the right subclause/issue pair."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call:
        with mock_commit as commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert commit.call_args[0] == (["33.4.1.5"], [42])


def test_no_deps_warns_when_no_changes(capsys) -> None:
    """No-deps mutator warns when no source-tree changes were made."""
    mock_call, mock_commit = _patched_call_and_commit(committed=False)
    with mock_call:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert "no source-tree changes" in capsys.readouterr().err


def test_no_deps_logs_subclause_to_stderr(capsys) -> None:
    """No-deps mutator prints a one-line banner to stderr."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert "§33.4.1.5" in capsys.readouterr().err


# --- build_with_deps_prompt -------------------------------------------------


def test_with_deps_prompt_mentions_subclause() -> None:
    """With-deps prompt mentions the target subclause."""
    prompt = build_with_deps_prompt(
        "33.4", "~/LRM.pdf", _failing_diagnostic(), [],
    )
    assert "§33.4" in prompt


def test_with_deps_prompt_includes_diagnostic_failures() -> None:
    """With-deps prompt embeds the diagnostic failure descriptions."""
    prompt = build_with_deps_prompt(
        "33.4", "~/LRM.pdf", _failing_diagnostic(), [],
    )
    assert "rule 7 has no production code" in prompt


def test_with_deps_prompt_lists_satisfied_deps() -> None:
    """With-deps prompt lists the dependencies that are already satisfied."""
    prompt = build_with_deps_prompt(
        "33.4", "~/LRM.pdf", _failing_diagnostic(),
        ["33.6.1", "33.4.1.5"],
    )
    assert "§33.6.1" in prompt and "§33.4.1.5" in prompt


def test_with_deps_prompt_describes_dep_reuse() -> None:
    """With-deps prompt explains that satisfied deps may be referenced."""
    prompt = build_with_deps_prompt(
        "33.4", "~/LRM.pdf", _failing_diagnostic(), ["33.6.1"],
    )
    assert "reference their machinery" in prompt


def test_with_deps_prompt_handles_empty_deps() -> None:
    """With-deps prompt handles the empty dependency list with a no-deps note."""
    prompt = build_with_deps_prompt(
        "33.4", "~/LRM.pdf", _failing_diagnostic(), [],
    )
    assert "No external dependencies" in prompt


def test_with_deps_prompt_forbids_git() -> None:
    """With-deps prompt explicitly forbids running git."""
    prompt = build_with_deps_prompt(
        "33.4", "~/LRM.pdf", _failing_diagnostic(), [],
    )
    assert "git" in prompt


# --- satisfy_unsatisfied_subclause_with_satisfied_dependencies --------------


def test_with_deps_skips_when_satisfied() -> None:
    """With-deps mutator is a no-op when the diagnostic is already satisfied."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(failing=False, subclause="33.4"),
                "~/LRM.pdf", ["33.6.1"], model="opus",
            )
    assert not call.called


def test_with_deps_invokes_mutator_when_failing() -> None:
    """With-deps mutator invokes run_mutator_call when failing."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"),
                "~/LRM.pdf", ["33.6.1"], model="opus",
            )
    assert call.called


def test_with_deps_passes_deps_into_prompt() -> None:
    """With-deps mutator forwards the deps list into the Claude prompt."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"),
                "~/LRM.pdf", ["33.6.1"], model="opus",
            )
    assert "§33.6.1" in call.call_args[0][0]


def test_with_deps_commits_with_subclause_and_issue() -> None:
    """With-deps mutator commits with the right subclause/issue pair."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call:
        with mock_commit as commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"),
                "~/LRM.pdf", ["33.6.1"], model="opus",
            )
    assert commit.call_args[0] == (["33.4"], [42])


def test_with_deps_logs_subclause_to_stderr(capsys) -> None:
    """With-deps mutator prints a one-line banner to stderr."""
    mock_call, mock_commit = _patched_call_and_commit()
    with mock_call:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"),
                "~/LRM.pdf", ["33.6.1"], model="opus",
            )
    assert "§33.4" in capsys.readouterr().err


# --- build_cycle_prompt -----------------------------------------------------


def _two_member_cycle():
    """Return a two-member CycleMember list with failing diagnostics."""
    return [
        CycleMember(
            subclause="33.4.1.5",
            diagnostic=_failing_diagnostic(),
            issue=10,
        ),
        CycleMember(
            subclause="33.4.1.6",
            diagnostic=_failing_diagnostic(),
            issue=11,
        ),
    ]


def test_cycle_prompt_lists_each_member() -> None:
    """Cycle prompt names each cycle member with the section sign."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", [])
    assert "§33.4.1.5" in prompt and "§33.4.1.6" in prompt


def test_cycle_prompt_describes_cycle_relationship() -> None:
    """Cycle prompt explains that cycle members must be implemented together."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", [])
    assert "implemented together" in prompt


def test_cycle_prompt_lists_each_diagnostic() -> None:
    """Cycle prompt embeds a DIAGNOSTIC section per cycle member."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", [])
    assert prompt.count("DIAGNOSTIC for") == 2


def test_cycle_prompt_includes_failure() -> None:
    """Cycle prompt includes each member's failure descriptions."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", [])
    assert "rule 7 has no production code" in prompt


def test_cycle_prompt_lists_external_deps() -> None:
    """Cycle prompt lists the external dependencies that are already satisfied."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", ["33.6.1"])
    assert "§33.6.1" in prompt


def test_cycle_prompt_handles_no_external_deps() -> None:
    """Cycle prompt handles the no-external-deps case with a notice."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", [])
    assert "No external dependencies" in prompt


def test_cycle_prompt_forbids_git() -> None:
    """Cycle prompt explicitly forbids running git."""
    prompt = build_cycle_prompt(_two_member_cycle(), "~/LRM.pdf", [])
    assert "git" in prompt


# --- satisfy_unsatisfied_subclause_set_with_satisfied_dependencies ---------


def _patched_cycle_runners(committed=True):
    """Patch run_mutator_call and commit_mutator_result for cycle tests."""
    return (
        patch("satisfy_subclause.mutators.run_mutator_call"),
        patch(
            "satisfy_subclause.mutators.commit_mutator_result",
            return_value=committed,
        ),
    )


def test_cycle_rejects_single_member() -> None:
    """A one-member 'cycle' is rejected."""
    members = [_two_member_cycle()[0]]
    with pytest.raises(ValueError):
        satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
            members, "~/LRM.pdf", [], model="opus",
        )


def test_cycle_rejects_four_members() -> None:
    """A four-member cycle exceeds the cap and is rejected."""
    members = _two_member_cycle() + _two_member_cycle()
    with pytest.raises(ValueError):
        satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
            members, "~/LRM.pdf", [], model="opus",
        )


def _mixed_cycle(member_a_diag, member_b_diag) -> list:
    """Build a two-member cycle whose diagnostics may differ."""
    return [
        CycleMember(subclause="33.4.1.5", diagnostic=member_a_diag, issue=10),
        CycleMember(subclause="33.4.1.6", diagnostic=member_b_diag, issue=11),
    ]


def test_cycle_skips_when_all_members_satisfied() -> None:
    """Cycle mutator is a no-op when every member is already satisfied."""
    members = _mixed_cycle(_all_satisfied(), _all_satisfied())
    mock_call, mock_commit = _patched_cycle_runners()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                members, "~/LRM.pdf", [], model="opus",
            )
    assert not call.called


def test_cycle_invokes_mutator_when_any_member_fails() -> None:
    """Cycle mutator invokes the Claude mutator when any member is failing."""
    members = _mixed_cycle(_failing_diagnostic(), _all_satisfied())
    mock_call, mock_commit = _patched_cycle_runners()
    with mock_call as call:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                members, "~/LRM.pdf", [], model="opus",
            )
    assert call.called


def test_cycle_commits_with_all_issues() -> None:
    """Cycle mutator commits with one Closes trailer per cycle member."""
    members = _two_member_cycle()
    mock_call, mock_commit = _patched_cycle_runners()
    with mock_call:
        with mock_commit as commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                members, "~/LRM.pdf", [], model="opus",
            )
    assert commit.call_args[0] == (["33.4.1.5", "33.4.1.6"], [10, 11])


def test_cycle_warns_when_no_changes(capsys) -> None:
    """Cycle mutator warns when no source-tree changes were made."""
    mock_call, mock_commit = _patched_cycle_runners(committed=False)
    with mock_call:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert "produced no source" in capsys.readouterr().err


def test_cycle_logs_subclauses_to_stderr(capsys) -> None:
    """Cycle mutator prints a one-line banner to stderr."""
    mock_call, mock_commit = _patched_cycle_runners()
    with mock_call:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    err = capsys.readouterr().err
    assert "33.4.1.5" in err and "33.4.1.6" in err
