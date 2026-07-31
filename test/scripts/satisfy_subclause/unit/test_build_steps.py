"""Unit tests for satisfy_subclause.mutators.build_steps."""

from satisfy_subclause.mutators import build_steps


def _step_descriptions(steps: list[tuple[str, str]]) -> list[str]:
    """Return just the description strings from a list of step pairs."""
    return [d for d, _p in steps]


_SIX_STEP_DESCRIPTIONS = [
    "Auditing src",
    "Auditing tests",
    "Deleting duplicate tests",
    "Deleting tests for non-normative subclauses",
    "Writing missing tests",
    "Writing missing functionality",
]


def test_build_steps_returns_six() -> None:
    """build_steps for a single subclause returns six step pairs."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert len(steps) == 6


def test_build_steps_descriptions_match_pipeline() -> None:
    """The six descriptions are the audit-then-act pipeline names."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert _step_descriptions(steps) == _SIX_STEP_DESCRIPTIONS


def test_build_steps_omits_move_misplaced_step() -> None:
    """The cross-clause "Moving misplaced tests" step is gone — local cleanups only."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all("Moving" not in description for description, _p in steps)


def test_build_steps_omits_rename_suites_step() -> None:
    """The suite-rename step is retired: no clause-numbered suite names remain."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all(description != "Renaming test suites" for description, _p in steps)


def test_build_steps_omits_rename_names_step() -> None:
    """The test-name-rename step is retired: no clause-numbered test names remain."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all(description != "Renaming test names" for description, _p in steps)


def test_build_steps_first_step_reads_lrm() -> None:
    """Step 1 includes the LRM read instruction for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "~/LRM.pdf" in steps[0][1]


def test_build_steps_first_step_audits_src() -> None:
    """Step 1 instructs Claude to audit src/."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "search src/" in steps[0][1]


def test_build_steps_second_step_audits_tests() -> None:
    """Step 2 instructs Claude to audit the canonical test files for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[1][1]


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


def test_build_steps_canonical_files_listed_in_writing_missing_tests() -> None:
    """The 'writing missing tests' step names the canonical test files."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[4][1]


def test_build_steps_non_normative_deletion_is_a_step() -> None:
    """A step targets non-normative-subclause test deletion."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert steps[3][0] == "Deleting tests for non-normative subclauses"


def test_build_steps_non_normative_deletion_mentions_normative_rules() -> None:
    """The non-normative-deletion step frames the criterion as 'no normative rules of its own'."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "no normative rules of its own" in steps[3][1]


def test_build_steps_non_normative_deletion_names_descriptive_examples() -> None:
    """The non-normative-deletion step names introductions/overviews/roadmaps as worked examples."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    prompt = steps[3][1]
    assert (
        "introductions" in prompt
        and "overviews" in prompt
        and "roadmaps" in prompt
    )


def test_build_steps_non_normative_deletion_lists_canonical_files() -> None:
    """The non-normative-deletion step lists the canonical test files for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[3][1]


def test_build_steps_omits_empty_file_deletion_step() -> None:
    """The empty-file-deletion step is retired: the CI gate catches a corpse file."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all(description != "Deleting empty test files" for description, _p in steps)


def test_build_steps_leaves_cmakelists_to_the_ci_gate() -> None:
    """No step spends a model turn editing test/CMakeLists.txt."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all("add_unit_test" not in prompt for _d, prompt in steps)


# --- canonical-file scope (Fix 1) -------------------------------------------


def test_constraints_forbid_non_canonical_edits() -> None:
    """The constraints block restricts edits to the subclause's canonical files."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "canonical files" in steps[0][1]


def test_constraints_name_canonical_test_files() -> None:
    """The constraints block names the canonical test files by path."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[0][1]


def test_audit_tests_step_searches_canonical_files() -> None:
    """The audit-tests step searches only the canonical test files for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "canonical test files" in steps[1][1]


def test_audit_tests_step_does_not_walk_full_unit_dir() -> None:
    """The audit-tests step no longer instructs Claude to walk the full test/src/unit/ tree."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "Search all files in test/src/unit/" not in steps[1][1]


def test_dedup_step_scoped_to_canonical_files() -> None:
    """The dedup step scope-limits to the canonical files for the subclause."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "canonical" in steps[2][1].lower()


# --- enumeration-driven audit (Fix 2) ---------------------------------------


def test_audit_src_step_requires_normative_enumeration() -> None:
    """The audit-src step instructs Claude to enumerate normative claims first."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "enumerate" in steps[0][1].lower()


def test_audit_src_step_calls_out_bnf_productions() -> None:
    """The audit-src enumeration explicitly names BNF productions as items to enumerate."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "BNF production" in steps[0][1]


def test_audit_src_step_calls_out_shall_sentences() -> None:
    """The audit-src enumeration explicitly names 'shall' sentences as items to enumerate."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "shall" in steps[0][1]


def test_audit_tests_step_references_enumeration() -> None:
    """The audit-tests step ties its work to the enumeration produced in the prior step."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "enumerated" in steps[1][1].lower()


def test_writing_missing_functionality_step_works_enumeration() -> None:
    """The missing-functionality step works the enumeration to completion."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "enumeration" in steps[5][1].lower()


def test_build_steps_constraints_open_the_session() -> None:
    """The step that opens the session carries the constraints block."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "Only act on requirements" in steps[0][1]


def test_build_steps_constraints_sent_once_per_pass() -> None:
    """Exactly one step carries the constraints block; the rest continue that session."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert sum(
        "Only act on requirements" in prompt for _d, prompt in steps
    ) == 1


def test_build_steps_no_excludes_machinery() -> None:
    """No step uses the implement_subclause --exclude framing."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps:
        assert "OFF-LIMITS" not in prompt


# --- cycle (multi-subclause) shape ------------------------------------------


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


# --- copyright wording + positive instructions ------------------------------


def test_build_steps_no_negative_do_not_in_oracles() -> None:
    """No step uses the 'Do NOT' negative phrasing."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps:
        assert "Do NOT" not in prompt


def test_build_steps_every_step_calls_out_lrm_copyright() -> None:
    """Every step names the LRM copyright concern, block or reminder.

    Without the explanation in the prompt, recent §13.5.2 and §4.7
    commits added comments that quoted the LRM verbatim. Naming the
    copyright concern in every step gives Claude the WHY for
    paraphrasing in source/test comments, not just commit messages,
    which is why the reminder carries it as well as the block.
    """
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all("copyrighted" in prompt for _d, prompt in steps)


# --- input-form + interaction coverage (blind-spot fix) ---------------------


def test_audit_src_enumerates_input_forms() -> None:
    """Step 1 asks Claude to enumerate each claim's distinct INPUT FORMS."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "INPUT FORMS" in steps[0][1]


def test_audit_src_enumerates_negative_form() -> None:
    """Step 1 asks for each rule's NEGATIVE (must-reject) form too."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "NEGATIVE form" in steps[0][1]


def test_audit_src_names_constant_expression_forms() -> None:
    """Step 1 names the 11.2.1 constant forms so parameter widths get covered."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    prompt = steps[0][1]
    assert (
        "11.2.1" in prompt
        and "a parameter" in prompt
        and "a localparam" in prompt
    )


def test_audit_src_enumerates_consumed_dependencies() -> None:
    """Step 1 asks which dependency subclauses' constructs the rule consumes."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "CONSUMES" in steps[0][1]


def test_constraints_require_full_pipeline_when_input_produced() -> None:
    """The constraints require a full-pipeline test when input production matters."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "full pipeline" in steps[0][1]


def test_constraints_allow_dependency_syntax_without_scope_violation() -> None:
    """Building input from a dependency's real syntax is declared scope-legal."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "does NOT violate the scoping rule" in steps[0][1]


def test_writing_tests_covers_each_input_form() -> None:
    """The writing-missing-tests step requires one test per enumerated input form."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    prompt = steps[4][1]
    assert (
        "per enumerated INPUT FORM" in prompt
        and "a literal AND a parameter" in prompt
    )


def test_writing_tests_covers_negative_form() -> None:
    """The writing-missing-tests step requires the negative (rejected-input) test."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "NEGATIVE form" in steps[4][1]


def test_writing_tests_requires_dependency_composed_end_to_end() -> None:
    """The writing-missing-tests step requires an end-to-end test per consumed dependency."""
    steps = build_steps(
        ["7.12.3"], "~/LRM.pdf", satisfied_dependencies=["7.5", "10.10"],
    )
    prompt = steps[4][1]
    assert "END-TO-END test" in prompt and "full pipeline" in prompt


# --- verification ownership -------------------------------------------------
#
# Framed as what the mutator owns rather than as a list of forbidden
# commands: naming the build tools in the prompt is what puts them in
# the model's head in the first place. The deny hook, not the prose, is
# what makes a build unreachable.


def test_constraints_end_the_pass_at_the_last_edit() -> None:
    """The constraints declare the saved file contents to be the deliverable."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "ends at the last edit you save" in steps[0][1]


def test_constraints_establish_correctness_by_reading() -> None:
    """The constraints direct the mutator to verify by inspection."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "Establish correctness by reading" in steps[0][1]


def test_constraints_name_ci_as_what_compiles() -> None:
    """The constraints name CI, not the orchestrator, as what compiles and tests."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "CI compiles the tree" in steps[0][1]


def test_constraints_place_the_report_after_the_campaign() -> None:
    """The constraints say CI's report is read after the campaign, not before the next pass."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "read after the wider campaign" in steps[0][1]


def test_verification_framing_is_not_repeated_after_the_first_step() -> None:
    """The verification-ownership prose is sent once, not restated per step."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert not any("CI compiles the tree" in prompt for _d, prompt in steps[1:])


# --- shared production functions and pinned test values ---------------------
#
# A rule can require a value from a function that a test for another
# subclause already pins differently. Left unaddressed, the improvised
# answer is a parallel helper that keeps the old test green, which
# preserves whichever reading of the LRM was wrong and hides it. The
# permitted in-place edit leads, so the block does not read as a ban on
# touching shared code.


def test_constraints_permit_editing_a_shared_function_in_place() -> None:
    """The constraints allow editing a shared function when the pinned values survive."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "yours to change in place" in steps[0][1]


def test_constraints_report_a_contradicted_pinned_value() -> None:
    """A rule that would change another subclause's pinned value is reported, not worked around."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "state the contradiction in this step's output" in steps[0][1]


def test_constraints_name_the_function_file_and_values_in_the_report() -> None:
    """The report identifies what contradicts what, so a human can settle it."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "naming the function, the test file, and the two values" in steps[0][1]


def test_constraints_explain_that_one_quantity_has_one_definition() -> None:
    """The constraints give the reason a cross-subclause contradiction is a misreading."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "one quantity one definition" in steps[0][1]


def test_constraints_rule_out_a_parallel_function() -> None:
    """A second function preserving the pinned value is named as the wrong resolution."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "a second function carrying the new value" in steps[0][1]


def test_shared_function_guidance_is_not_repeated_after_the_first_step() -> None:
    """The shared-function guidance is sent once, not restated per step."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert not any("yours to change in place" in prompt for _d, prompt in steps[1:])


# --- constraints reminder on the continued steps ----------------------------
#
# The steps of one pass share a Claude session: step 1 opens it and the
# rest continue it. The block sent with step 1 is therefore still in
# context when a later step arrives, and re-sending it would restate
# several hundred unchanging words per step and bury each step's own
# instruction. A sentence naming the scope stands in its place.


def test_reminder_rides_on_every_continued_step() -> None:
    """Every step after the first points back at the constraints sent with the first."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all(
        "constraints sent with the first step" in prompt
        for _d, prompt in steps[1:]
    )


def test_reminder_absent_from_the_step_that_carries_the_block() -> None:
    """The step carrying the block does not also point back at it."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "constraints sent with the first step" not in steps[0][1]


def test_reminder_names_every_scope_member() -> None:
    """The reminder names each subclause of a multi-member pass, not just the first."""
    steps = build_steps(
        ["33.4.1.5", "33.4.1.6"], "~/LRM.pdf", satisfied_dependencies=[],
    )
    assert "act on §33.4.1.5, §33.4.1.6 alone" in steps[1][1]


def test_reminder_keeps_the_saved_files_as_the_deliverable() -> None:
    """The reminder pins the deliverable on the files an action step saves.

    Read against steps[2], the first step that saves anything. The two
    steps before it audit, and their deliverable is a report.
    """
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "save as the deliverable" in steps[2][1]


def test_constraints_name_the_audit_deliverable_as_the_report() -> None:
    """The block sent with the audit-src step calls its enumeration the deliverable."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "enumeration you report in your reply" in steps[0][1]


def test_constraints_scope_the_editing_claim_past_the_audits() -> None:
    """The block claims editing is the only action from the third step on."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "From the third step on your only action" in steps[0][1]


def test_audit_tests_step_delivers_its_enumeration() -> None:
    """The audit-tests reminder names the reported enumeration as the deliverable."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "report this step's enumeration in your reply" in steps[1][1]


def test_audit_tests_step_is_not_told_files_are_its_deliverable() -> None:
    """The audit-tests step is never told the files it saves are what it owes."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "save as the deliverable" not in steps[1][1]


def test_scoping_prose_is_not_repeated_after_the_first_step() -> None:
    """The block's scoping paragraph is sent once, not restated per step."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert not any(
        "A requirement belongs to the subclause" in prompt
        for _d, prompt in steps[1:]
    )
