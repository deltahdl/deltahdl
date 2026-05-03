"""Unit tests for satisfy_subclause.mutators."""

from unittest.mock import patch

import pytest

from satisfy_subclause.mutators import (
    MUTATOR_DISALLOWED_TOOLS,
    CycleMember,
    build_commit_message,
    build_steps,
    filter_changes,
    is_valid_path,
    run_step,
    run_steps,
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_without_dependencies,
)


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


def test_disallowed_tools_blocks_pdftotext() -> None:
    """The mutator disallowed-tools list blocks Bash(pdftotext *)."""
    assert "pdftotext" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pdfgrep() -> None:
    """The mutator disallowed-tools list blocks Bash(pdfgrep *)."""
    assert "pdfgrep" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pdftohtml() -> None:
    """The mutator disallowed-tools list blocks Bash(pdftohtml *)."""
    assert "pdftohtml" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pdftoppm() -> None:
    """The mutator disallowed-tools list blocks Bash(pdftoppm *)."""
    assert "pdftoppm" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_mutool() -> None:
    """The mutator disallowed-tools list blocks Bash(mutool *)."""
    assert "mutool" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_allows_rm() -> None:
    """Steps 4 and 6 require deleting files on disk; rm must not be blocked."""
    assert "Bash(rm *)" not in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_allows_mv() -> None:
    """Step 4 (Moving misplaced tests) needs mv; it must not be blocked."""
    assert "Bash(mv *)" not in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_allows_cp() -> None:
    """cp is not destructive and is dropped for symmetry with rm/mv."""
    assert "Bash(cp *)" not in MUTATOR_DISALLOWED_TOOLS


# --- run_step ---------------------------------------------------------------


def _patched_streaming():
    """Patch run_claude_streaming; the stub returns an empty result string."""
    return patch(
        "satisfy_subclause.mutators.run_claude_streaming_with_retry",
        return_value="",
    )


def test_run_step_passes_prompt() -> None:
    """run_step forwards the prompt to the streaming runner."""
    with _patched_streaming() as mock_stream:
        run_step("hello prompt", model="opus", continue_session=False)
    assert mock_stream.call_args[0][1] == "hello prompt"


def test_run_step_passes_model() -> None:
    """run_step passes --model to the Claude CLI."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="haiku", continue_session=False)
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_step_passes_disallowed_tools() -> None:
    """run_step passes --disallowedTools."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "--disallowedTools" in mock_stream.call_args[0][0]


def test_run_step_uses_dangerously_skip_permissions() -> None:
    """run_step passes --dangerously-skip-permissions."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "--dangerously-skip-permissions" in mock_stream.call_args[0][0]


def test_run_step_uses_stream_json() -> None:
    """run_step requests stream-json output for live streaming."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    cmd = mock_stream.call_args[0][0]
    assert cmd[cmd.index("--output-format") + 1] == "stream-json"


def test_run_step_uses_verbose() -> None:
    """run_step passes --verbose (required by stream-json)."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "--verbose" in mock_stream.call_args[0][0]


def test_run_step_first_step_does_not_continue() -> None:
    """The first step opens a fresh Claude session (no --continue)."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "--continue" not in mock_stream.call_args[0][0]


def test_run_step_later_step_continues_session() -> None:
    """Later steps resume the session via --continue."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=True)
    assert "--continue" in mock_stream.call_args[0][0]


def test_run_step_passes_env() -> None:
    """run_step passes a Claude-safe env to the streaming runner."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "env" in mock_stream.call_args[1]


# --- run_steps --------------------------------------------------------------


def test_run_steps_invokes_each_step() -> None:
    """run_steps calls run_step once per step."""
    steps = [("desc1", "p1"), ("desc2", "p2"), ("desc3", "p3")]
    with patch("satisfy_subclause.mutators.run_step") as mock_step:
        run_steps(steps, model="opus")
    assert mock_step.call_count == 3


def test_run_steps_first_step_opens_fresh_session() -> None:
    """The first run_step call has continue_session=False."""
    steps = [("desc1", "p1"), ("desc2", "p2")]
    with patch("satisfy_subclause.mutators.run_step") as mock_step:
        run_steps(steps, model="opus")
    assert mock_step.call_args_list[0][1]["continue_session"] is False


def test_run_steps_later_steps_continue_session() -> None:
    """Every step after the first has continue_session=True."""
    steps = [("desc1", "p1"), ("desc2", "p2"), ("desc3", "p3")]
    with patch("satisfy_subclause.mutators.run_step") as mock_step:
        run_steps(steps, model="opus")
    assert all(
        call[1]["continue_session"] is True
        for call in mock_step.call_args_list[1:]
    )


def test_run_steps_passes_model() -> None:
    """run_steps forwards the model argument to each run_step call."""
    steps = [("desc", "p")]
    with patch("satisfy_subclause.mutators.run_step") as mock_step:
        run_steps(steps, model="haiku")
    assert mock_step.call_args[1]["model"] == "haiku"


def test_run_steps_passes_prompt() -> None:
    """run_steps forwards each step's prompt to run_step."""
    steps = [("only", "a-prompt")]
    with patch("satisfy_subclause.mutators.run_step") as mock_step:
        run_steps(steps, model="opus")
    assert mock_step.call_args[0][0] == "a-prompt"


def test_run_steps_logs_first_step_banner(capsys) -> None:
    """run_steps prints a 'Step 1/total: description' banner for step 1."""
    steps = [("Auditing src", "p1"), ("Auditing tests", "p2")]
    with patch("satisfy_subclause.mutators.run_step"):
        run_steps(steps, model="opus")
    assert "Step 1/2: Auditing src" in capsys.readouterr().out


def test_run_steps_logs_later_step_banner(capsys) -> None:
    """run_steps prints a 'Step 2/total: description' banner for step 2."""
    steps = [("Auditing src", "p1"), ("Auditing tests", "p2")]
    with patch("satisfy_subclause.mutators.run_step"):
        run_steps(steps, model="opus")
    assert "Step 2/2: Auditing tests" in capsys.readouterr().out


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
    """A multi-subclause commit title is labelled neutrally."""
    msg = build_commit_message(["33.4.1.5", "33.4.1.6"], [10, 11], "")
    assert "multi-subclause pass" in msg


def test_build_commit_message_set_title_avoids_cycle_assertion() -> None:
    """A multi-subclause commit title does not assert co-implementation."""
    msg = build_commit_message(["33.4.1.5", "33.4.1.6"], [10, 11], "")
    assert "cycle co-implementation" not in msg


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


# --- build_steps ------------------------------------------------------------


def _step_descriptions(steps) -> list[str]:
    """Return just the description strings from a list of step pairs."""
    return [d for d, _p in steps]


_TEN_STEP_DESCRIPTIONS = [
    "Auditing src",
    "Auditing tests",
    "Deleting duplicate tests",
    "Moving misplaced tests",
    "Deleting tests for non-normative subclauses",
    "Deleting empty test files",
    "Renaming test suites",
    "Renaming test names",
    "Writing missing tests",
    "Writing missing functionality",
]


def test_build_steps_returns_ten() -> None:
    """build_steps for a single subclause returns ten step pairs."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert len(steps) == 10


def test_build_steps_descriptions_match_pipeline() -> None:
    """The ten descriptions are the audit-then-act pipeline names."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert _step_descriptions(steps) == _TEN_STEP_DESCRIPTIONS


def test_build_steps_first_step_reads_lrm() -> None:
    """Step 1 includes the LRM read instruction for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "~/LRM.pdf" in steps[0][1]


def test_build_steps_first_step_audits_src() -> None:
    """Step 1 instructs Claude to audit src/."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "search src/" in steps[0][1]


def test_build_steps_second_step_audits_tests() -> None:
    """Step 2 instructs Claude to audit test/src/unit/."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test/src/unit/" in steps[1][1]


def test_build_steps_no_deps_states_no_dependencies() -> None:
    """Step 1 with no deps says no external deps were needed."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "No external dependencies" in steps[0][1]


def test_build_steps_with_deps_lists_dependencies() -> None:
    """Step 1 with satisfied deps names them in the deps block."""
    steps = build_steps(
        ["33.4.1.5"], "~/LRM.pdf",
        satisfied_dependencies=["33.6.1", "33.4.1.4"],
    )
    assert "§33.6.1" in steps[0][1] and "§33.4.1.4" in steps[0][1]


def test_build_steps_with_deps_says_reference_them() -> None:
    """Step 1 with deps tells Claude they may be referenced."""
    steps = build_steps(
        ["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=["33.6.1"],
    )
    assert "reference their machinery" in steps[0][1]


def test_build_steps_no_json_contract() -> None:
    """No step asks for a JSON object diagnostic."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps:
        assert "JSON object" not in prompt


def test_build_steps_no_rule_coverage_token() -> None:
    """No step references the rule_coverage JSON-key from the dropped oracle."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all("rule_coverage" not in prompt for _d, prompt in steps)


def test_build_steps_no_satisfaction_predicate() -> None:
    """No step references the (a)-(e) satisfaction-predicate framing."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all(
        "satisfaction predicate" not in prompt for _d, prompt in steps
    )


def test_build_steps_canonical_files_listed_in_step_4() -> None:
    """Step 4 (moving misplaced tests) names the canonical test files."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[3][1]


def test_build_steps_canonical_files_listed_in_writing_missing_tests() -> None:
    """The 'writing missing tests' step names the canonical test files."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[8][1]


def test_build_steps_step5_is_non_normative_deletion() -> None:
    """Step 5's description targets non-normative-subclause test deletion."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert steps[4][0] == "Deleting tests for non-normative subclauses"


def test_build_steps_step5_mentions_normative_rules() -> None:
    """Step 5 frames the criterion as 'no normative rules of its own'."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "no normative rules of its own" in steps[4][1]


def test_build_steps_step5_names_descriptive_examples() -> None:
    """Step 5 names introductions/overviews/roadmaps as worked examples."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    prompt = steps[4][1]
    assert (
        "introductions" in prompt
        and "overviews" in prompt
        and "roadmaps" in prompt
    )


def test_build_steps_step5_lists_canonical_files() -> None:
    """Step 5 lists the canonical test files for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[4][1]


def test_build_steps_step6_is_empty_file_cleanup() -> None:
    """Step 6's description targets empty-test-file cleanup."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert steps[5][0] == "Deleting empty test files"


def test_build_steps_step6_removes_cmakelists_entry() -> None:
    """Step 6 instructs Claude to also remove the CMakeLists.txt entry."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "CMakeLists.txt" in steps[5][1]


def test_build_steps_step6_lists_canonical_files() -> None:
    """Step 6 names the canonical test files it inspects."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[5][1]


def test_build_steps_step4_no_inline_empty_file_rule() -> None:
    """Step 4 (Moving) no longer carries the inline empty-file rule."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "CMakeLists.txt" not in steps[3][1]


def test_build_steps_constraints_present_in_action_steps() -> None:
    """Every action step (3-8) includes the per-step constraints block."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps[2:]:
        assert "Only act on requirements" in prompt


def test_build_steps_no_excludes_machinery() -> None:
    """No step uses the implement_subclause --exclude framing."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps:
        assert "OFF-LIMITS" not in prompt


def test_build_steps_cycle_lists_each_member() -> None:
    """Cycle steps name every cycle member in step 1."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "§33.4.1.5" in steps[0][1] and "§33.4.1.6" in steps[0][1]


def test_build_steps_cycle_describes_one_pass() -> None:
    """Step 1 of a multi-subclause run says it satisfies them in one pass."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "in one pass" in steps[0][1]


def test_build_steps_cycle_invites_weaving_or_independent_satisfaction() -> None:
    """Step 1 frames weaving and independent satisfaction as equal options."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "weave" in steps[0][1]


def test_build_steps_cycle_does_not_assert_mutual_dependency() -> None:
    """Step 1 does not claim each member requires machinery from the others."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "requires machinery from the others" not in steps[0][1]


def test_build_steps_cycle_lists_first_member_canonical_files() -> None:
    """Cycle steps list canonical test files for the first cycle member."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "test_parser_clause_33_04_01_05.cpp" in steps[1][1]


def test_build_steps_cycle_lists_second_member_canonical_files() -> None:
    """Cycle steps list canonical test files for the second cycle member."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "test_parser_clause_33_04_01_06.cpp" in steps[1][1]


def test_build_steps_cycle_no_per_member_diagnostic() -> None:
    """Cycle steps no longer carry the per-member DIAGNOSTIC blocks."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    for _description, prompt in steps:
        assert "DIAGNOSTIC for" not in prompt


def test_build_steps_cycle_external_deps_listed() -> None:
    """Cycle step 1 lists external dependencies if any."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf",
        satisfied_dependencies=["33.6.1"],
    )
    assert "§33.6.1" in steps[0][1]


def test_build_steps_single_member_has_no_cycle_intro() -> None:
    """A single-subclause run skips the multi-subclause weaving preface."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "weave" not in steps[0][1]


# --- mutator dispatch shells ------------------------------------------------


def _patched_run_steps_and_commit(committed=True):
    """Patch run_steps and commit_mutator_result."""
    return (
        patch("satisfy_subclause.mutators.run_steps"),
        patch(
            "satisfy_subclause.mutators.commit_mutator_result",
            return_value=committed,
        ),
    )


def _target(subclause: str = "33.4.1.5", issue: int = 42) -> CycleMember:
    """Build a CycleMember target for mutator-shell tests."""
    return CycleMember(subclause=subclause, issue=issue)


# --- satisfy_unsatisfied_subclause_without_dependencies ---------------------


def test_no_deps_invokes_run_steps() -> None:
    """No-deps mutator runs the eight-step pipeline."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert run.called


def test_no_deps_passes_ten_steps() -> None:
    """No-deps mutator hands ten step pairs to run_steps."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert len(run.call_args[0][0]) == 10


def test_no_deps_passes_model() -> None:
    """No-deps mutator forwards the model arg to run_steps."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="haiku",
            )
    assert run.call_args[1]["model"] == "haiku"


def test_no_deps_commits_with_subclause_and_issue() -> None:
    """No-deps mutator commits with the right subclause/issue pair."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run:
        with mock_commit as commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert commit.call_args[0] == (["33.4.1.5"], [42])


def test_no_deps_warns_when_no_changes(capsys) -> None:
    """No-deps mutator warns when no source-tree changes were made."""
    mock_run, mock_commit = _patched_run_steps_and_commit(committed=False)
    with mock_run:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert "no source-tree changes" in capsys.readouterr().err


def test_no_deps_logs_subclause_to_stderr(capsys) -> None:
    """No-deps mutator prints a one-line banner to stderr."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run:
        with mock_commit:
            satisfy_unsatisfied_subclause_without_dependencies(
                _target(), "~/LRM.pdf", model="opus",
            )
    assert "§33.4.1.5" in capsys.readouterr().err


# --- satisfy_unsatisfied_subclause_with_satisfied_dependencies --------------


def test_with_deps_invokes_run_steps() -> None:
    """With-deps mutator runs the eight-step pipeline."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"), "~/LRM.pdf",
                ["33.6.1"], model="opus",
            )
    assert run.called


def test_with_deps_passes_ten_steps() -> None:
    """With-deps mutator hands ten step pairs to run_steps."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"), "~/LRM.pdf",
                ["33.6.1"], model="opus",
            )
    assert len(run.call_args[0][0]) == 10


def test_with_deps_passes_deps_into_first_step_prompt() -> None:
    """With-deps mutator embeds the deps list in step 1's prompt."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"), "~/LRM.pdf",
                ["33.6.1"], model="opus",
            )
    first_step_prompt = run.call_args[0][0][0][1]
    assert "§33.6.1" in first_step_prompt


def test_with_deps_commits_with_subclause_and_issue() -> None:
    """With-deps mutator commits with the right subclause/issue pair."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run:
        with mock_commit as commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"), "~/LRM.pdf",
                ["33.6.1"], model="opus",
            )
    assert commit.call_args[0] == (["33.4"], [42])


def test_with_deps_warns_when_no_changes(capsys) -> None:
    """With-deps mutator warns when no source-tree changes were made."""
    mock_run, mock_commit = _patched_run_steps_and_commit(committed=False)
    with mock_run:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"), "~/LRM.pdf",
                ["33.6.1"], model="opus",
            )
    assert "no source-tree changes" in capsys.readouterr().err


def test_with_deps_logs_subclause_to_stderr(capsys) -> None:
    """With-deps mutator prints a one-line banner to stderr."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run:
        with mock_commit:
            satisfy_unsatisfied_subclause_with_satisfied_dependencies(
                _target(subclause="33.4"), "~/LRM.pdf",
                ["33.6.1"], model="opus",
            )
    assert "§33.4" in capsys.readouterr().err


# --- satisfy_unsatisfied_subclause_set_with_satisfied_dependencies ---------


def _two_member_cycle() -> list[CycleMember]:
    """Return a two-member CycleMember list."""
    return [
        CycleMember(subclause="33.4.1.5", issue=10),
        CycleMember(subclause="33.4.1.6", issue=11),
    ]


def test_cycle_rejects_single_member() -> None:
    """A one-member 'cycle' is rejected."""
    members = [_two_member_cycle()[0]]
    with pytest.raises(ValueError):
        satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
            members, "~/LRM.pdf", [], model="opus",
        )


def test_cycle_accepts_three_members() -> None:
    """A three-member cycle runs the eight-step pipeline."""
    three = _two_member_cycle() + [CycleMember(subclause="33.5", issue=12)]
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                three, "~/LRM.pdf", [], model="opus",
            )
    assert run.called


def _four_member_cycle() -> list[CycleMember]:
    """Return a four-member CycleMember list."""
    return [
        CycleMember(subclause="33.4.1.5", issue=10),
        CycleMember(subclause="33.4.1.6", issue=11),
        CycleMember(subclause="33.4.1.7", issue=12),
        CycleMember(subclause="33.4.1.8", issue=13),
    ]


def test_cycle_accepts_four_members() -> None:
    """A four-member cycle runs the eight-step pipeline."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _four_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert run.called


def test_cycle_accepts_five_members() -> None:
    """A five-member cycle runs the eight-step pipeline."""
    five = _four_member_cycle() + [CycleMember(subclause="33.5", issue=14)]
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                five, "~/LRM.pdf", [], model="opus",
            )
    assert run.called


def test_cycle_four_members_skips_pipeline_cycle_label() -> None:
    """A four-member cycle no longer tags issues with the pipeline-cycle label."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with patch("satisfy_subclause.mutators.subprocess.run") as proc:
        with mock_run:
            with mock_commit:
                satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                    _four_member_cycle(), "~/LRM.pdf", [], model="opus",
                )
    labelled_with_pipeline_cycle = [
        call for call in proc.call_args_list
        if call.args and "pipeline-cycle" in str(call.args[0])
    ]
    assert labelled_with_pipeline_cycle == []


def test_cycle_invokes_run_steps() -> None:
    """Cycle mutator runs the eight-step pipeline."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert run.called


def test_cycle_passes_ten_steps() -> None:
    """Cycle mutator hands ten step pairs to run_steps."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert len(run.call_args[0][0]) == 10


def test_cycle_first_step_lists_first_member() -> None:
    """Cycle mutator's first-step prompt names the first cycle member."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert "§33.4.1.5" in run.call_args[0][0][0][1]


def test_cycle_first_step_lists_second_member() -> None:
    """Cycle mutator's first-step prompt names the second cycle member."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert "§33.4.1.6" in run.call_args[0][0][0][1]


def test_cycle_first_step_lists_external_deps() -> None:
    """Cycle mutator's first-step prompt lists external satisfied deps."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run as run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", ["33.6.1"], model="opus",
            )
    first_step_prompt = run.call_args[0][0][0][1]
    assert "§33.6.1" in first_step_prompt


def test_cycle_commits_with_all_issues() -> None:
    """Cycle mutator commits with one Closes trailer per cycle member."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run:
        with mock_commit as commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert commit.call_args[0] == (["33.4.1.5", "33.4.1.6"], [10, 11])


def test_cycle_warns_when_no_changes(capsys) -> None:
    """Cycle mutator warns when no source-tree changes were made."""
    mock_run, mock_commit = _patched_run_steps_and_commit(committed=False)
    with mock_run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    assert "produced no source" in capsys.readouterr().err


def test_cycle_logs_subclauses_to_stderr(capsys) -> None:
    """Cycle mutator prints a one-line banner to stderr."""
    mock_run, mock_commit = _patched_run_steps_and_commit()
    with mock_run:
        with mock_commit:
            satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
                _two_member_cycle(), "~/LRM.pdf", [], model="opus",
            )
    err = capsys.readouterr().err
    assert "33.4.1.5" in err and "33.4.1.6" in err


# --- CycleMember dataclass --------------------------------------------------


def test_cycle_member_holds_subclause() -> None:
    """CycleMember stores the subclause identifier."""
    member = CycleMember(subclause="33.4.1.5", issue=42)
    assert member.subclause == "33.4.1.5"


def test_cycle_member_holds_issue() -> None:
    """CycleMember stores the issue number."""
    member = CycleMember(subclause="33.4.1.5", issue=42)
    assert member.issue == 42


# --- run_step: retry-helper wiring ------------------------------------------


def test_run_step_passes_role_to_retry_helper() -> None:
    """The Step role is forwarded so retry warnings name it."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert mock_stream.call_args[1]["role"] == "Step"


def test_run_step_retry_cmd_uses_continue() -> None:
    """The retry_cmd handed to the helper appends --continue."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "--continue" in mock_stream.call_args[1]["retry_cmd"]


def test_run_step_retry_cmd_carries_disallowed_tools() -> None:
    """The retry_cmd carries the mutator disallowed-tools string."""
    with _patched_streaming() as mock_stream:
        run_step("prompt", model="opus", continue_session=False)
    assert "--disallowedTools" in mock_stream.call_args[1]["retry_cmd"]


# --- build_steps: copyright wording + positive instructions -----------------


def test_build_steps_constraints_omit_copyright() -> None:
    """The eight-step prompts must not carry the LRM copyright reason."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert not any("copyright" in p.lower() for _d, p in steps)


def test_build_steps_constraints_omit_paraphrase() -> None:
    """The eight-step prompts must not tell Claude to paraphrase."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert not any("paraphrase" in p.lower() for _d, p in steps)


def test_build_steps_no_negative_do_not_in_oracles() -> None:
    """No step uses the 'Do NOT' negative phrasing."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps:
        assert "Do NOT" not in prompt
