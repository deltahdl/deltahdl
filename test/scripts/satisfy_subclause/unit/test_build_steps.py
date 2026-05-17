"""Unit tests for satisfy_subclause.mutators.build_steps."""

from satisfy_subclause.mutators import build_steps

from lib.python.claude_cli_streaming import COPYRIGHT_REASON


def _step_descriptions(steps: list[tuple[str, str]]) -> list[str]:
    """Return just the description strings from a list of step pairs."""
    return [d for d, _p in steps]


_NINE_STEP_DESCRIPTIONS = [
    "Auditing src",
    "Auditing tests",
    "Deleting duplicate tests",
    "Deleting tests for non-normative subclauses",
    "Deleting empty test files",
    "Renaming test suites",
    "Renaming test names",
    "Writing missing tests",
    "Writing missing functionality",
]


def test_build_steps_returns_nine() -> None:
    """build_steps for a single subclause returns nine step pairs."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert len(steps) == 9


def test_build_steps_descriptions_match_pipeline() -> None:
    """The nine descriptions are the audit-then-act pipeline names."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert _step_descriptions(steps) == _NINE_STEP_DESCRIPTIONS


def test_build_steps_omits_move_misplaced_step() -> None:
    """The cross-clause "Moving misplaced tests" step is gone — local cleanups only."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert all("Moving" not in description for description, _p in steps)


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
    assert "test_parser_clause_33_04_01_05.cpp" in steps[7][1]


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


def test_build_steps_empty_file_cleanup_is_a_step() -> None:
    """A step targets empty-test-file cleanup."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert steps[4][0] == "Deleting empty test files"


def test_build_steps_empty_file_cleanup_removes_cmakelists_entry() -> None:
    """The empty-file-cleanup step instructs Claude to also remove the CMakeLists.txt entry."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "CMakeLists.txt" in steps[4][1]


def test_build_steps_empty_file_cleanup_lists_canonical_files() -> None:
    """The empty-file-cleanup step names the canonical test files it inspects."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[4][1]


# --- canonical-file scope (Fix 1) -------------------------------------------


def test_constraints_forbid_non_canonical_edits() -> None:
    """The per-step constraints block restricts edits to the subclause's canonical files."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "canonical files" in steps[2][1]


def test_constraints_name_canonical_test_files() -> None:
    """The constraints block names the canonical test files by path."""
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    assert "test_parser_clause_33_04_01_05.cpp" in steps[2][1]


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
    assert "enumeration" in steps[8][1].lower()


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


def test_build_steps_constraints_carry_copyright_reason() -> None:
    """Every action step's constraints carry the LRM copyright reason.

    Without the explanation in the prompt, recent §13.5.2 and §4.7
    commits added comments that quoted the LRM verbatim. Reusing the
    same COPYRIGHT_REASON the commit-body prompt uses gives Claude the
    WHY for paraphrasing in source/test comments, not just commit
    messages.
    """
    steps = build_steps(["33.4.1.5"], "~/LRM.pdf", satisfied_dependencies=[])
    for _description, prompt in steps[2:]:
        assert COPYRIGHT_REASON in prompt
