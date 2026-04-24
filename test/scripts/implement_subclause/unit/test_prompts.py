"""Unit tests for prompt generation across all clause depths."""


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _all_prompts(isc, subclause, lrm="~/LRM.pdf", **kwargs):
    """Join all step prompts into a single string for assertion."""
    steps = isc.build_steps(subclause, lrm, **kwargs)
    return " ".join(p for _, p in steps)


def _step_names(isc, subclause, lrm="~/LRM.pdf", **kwargs):
    """Return list of step description strings."""
    steps = isc.build_steps(subclause, lrm, **kwargs)
    return [name for name, _ in steps]


# ---------------------------------------------------------------------------
# Descendant scope boundary
# ---------------------------------------------------------------------------


class TestDescendantBoundary:
    """Tests for descendant subclause boundary enforcement."""

    def test_constraints_mention_descendant_boundary(self, isc):
        """Constraints explicitly forbid acting on descendant content."""
        prompt = _all_prompts(isc, "6.3")
        assert "descendant subclause" in prompt

    def test_constraints_list_descendant_example_1(self, isc):
        """Constraints give §X.1 descendant example."""
        prompt = _all_prompts(isc, "6.3")
        assert "§6.3.1" in prompt

    def test_constraints_list_descendant_example_2(self, isc):
        """Constraints give §X.2 descendant example."""
        prompt = _all_prompts(isc, "6.3")
        assert "§6.3.2" in prompt

    def test_exclude_note_labels_off_limits(self, isc):
        """Exclude note uses OFF-LIMITS SUBCLAUSES label."""
        prompt = _all_prompts(isc, "6.3", exclude="6.3.1,6.3.2")
        assert "OFF-LIMITS SUBCLAUSES" in prompt

    def test_exclude_note_names_first_descendant(self, isc):
        """Exclude note lists the first excluded subclause."""
        prompt = _all_prompts(isc, "6.3", exclude="6.3.1,6.3.2")
        assert "§6.3.1" in prompt

    def test_exclude_note_names_second_descendant(self, isc):
        """Exclude note lists the second excluded subclause."""
        prompt = _all_prompts(isc, "6.3", exclude="6.3.1,6.3.2")
        assert "§6.3.2" in prompt

    def test_exclude_note_names_leave_as_is(self, isc):
        """Exclude note tells Claude to leave descendant content as-is."""
        prompt = _all_prompts(isc, "6.3", exclude="6.3.1")
        assert "Leave their content exactly as-is" in prompt

    def test_no_exclude_omits_off_limits(self, isc):
        """Without --exclude, OFF-LIMITS label does not appear."""
        prompt = _all_prompts(isc, "6.3")
        assert "OFF-LIMITS SUBCLAUSES" not in prompt

    def test_no_audit_scope_step(self, isc):
        """No 'Auditing scope' step exists after removal."""
        names = _step_names(isc, "6.3")
        assert "Auditing scope" not in names


def _check_common_structure(prompt, subclause):
    """Return list of missing common structure elements."""
    missing = []
    if "unit tests" not in prompt:
        missing.append("unit tests")
    if "pipeline stages" not in prompt:
        missing.append("'pipeline stages'")
    if f"§{subclause}" not in prompt:
        missing.append(f"subclause '§{subclause}'")
    if "LRM prose" not in prompt:
        missing.append("copyright constraint")
    if "unintuitive" not in prompt:
        missing.append("rename unintuitive names")
    return missing


# ---------------------------------------------------------------------------
# Depth 1
# ---------------------------------------------------------------------------


class TestDepth1:
    """Tests for depth-1 prompt generation."""

    def test_numeric_includes_subclause(self, isc):
        """Numeric prompt includes the target subclause."""
        prompt = _all_prompts(isc,"4", "~/LRM.pdf")
        assert "§4" in prompt

    def test_annex_includes_subclause(self, isc):
        """Annex prompt includes the target subclause."""
        prompt = _all_prompts(isc,"B", "~/LRM.pdf")
        assert "§B" in prompt

    def test_numeric_has_common_structure(self, isc):
        """Numeric prompt has all common structure elements."""
        prompt = _all_prompts(isc,"4", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "4")

    def test_annex_has_common_structure(self, isc):
        """Annex prompt has all common structure elements."""
        prompt = _all_prompts(isc,"B", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "B")

    def test_uses_short_lrm_path(self, isc):
        """Prompt embeds the short LRM path."""
        prompt = _all_prompts(isc,"B", "~/LRM.pdf")
        assert "~/LRM.pdf" in prompt

    def test_depth_1_non_general_mentions_general_overview(self, isc):
        """Non-General depth-1 prompt reads General/Overview for context."""
        prompt = _all_prompts(isc, "4", "~/LRM.pdf")
        assert "General" in prompt

    def test_depth_1_general_omits_general_overview(self, isc):
        """X.1 (General) prompt does not read General/Overview."""
        steps = isc.build_steps("4.1", "~/LRM.pdf")
        assert "General or Overview" not in steps[0][1]


# ---------------------------------------------------------------------------
# Depth 2
# ---------------------------------------------------------------------------


class TestDepth2:
    """Tests for depth-2 prompt generation."""

    def test_numeric_has_common_structure(self, isc):
        """Numeric prompt has all common structure elements."""
        prompt = _all_prompts(isc,"4.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "4.1")

    def test_depth_2_non_general_mentions_general_overview(self, isc):
        """Non-General depth-2 prompt reads General/Overview for context."""
        prompt = _all_prompts(isc, "4.4", "~/LRM.pdf")
        assert "General" in prompt


# ---------------------------------------------------------------------------
# Depth 3
# ---------------------------------------------------------------------------


class TestDepth3:
    """Tests for depth-3 prompt generation."""

    def test_numeric_lists_ancestors(self, isc):
        """Numeric prompt lists ancestor subclauses."""
        prompt = _all_prompts(isc,"6.24.1", "~/LRM.pdf")
        assert "§6.24" in prompt

    def test_annex_lists_ancestors(self, isc):
        """Annex prompt lists ancestor subclauses."""
        prompt = _all_prompts(isc,"A.8.1", "~/LRM.pdf")
        assert "§A.8" in prompt

    def test_numeric_has_common_structure(self, isc):
        """Numeric prompt has all common structure elements."""
        prompt = _all_prompts(isc,"6.24.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "6.24.1")

    def test_annex_has_common_structure(self, isc):
        """Annex prompt has all common structure elements."""
        prompt = _all_prompts(isc,"A.8.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "A.8.1")


# ---------------------------------------------------------------------------
# Depth 4
# ---------------------------------------------------------------------------


class TestDepth4:
    """Tests for depth-4 prompt generation."""

    def test_numeric_lists_full_hierarchy(self, isc):
        """Numeric prompt lists all ancestor subclauses."""
        prompt = _all_prompts(isc,"4.4.3.1", "~/LRM.pdf")
        assert all(
            f"§{s}" in prompt
            for s in ["4.4", "4.4.3"]
        )

    def test_annex_lists_full_hierarchy(self, isc):
        """Annex prompt lists all ancestor subclauses."""
        prompt = _all_prompts(isc,"A.7.5.3", "~/LRM.pdf")
        assert all(
            f"§{s}" in prompt
            for s in ["A.7", "A.7.5"]
        )

    def test_has_common_structure(self, isc):
        """Prompt has all common structure elements."""
        prompt = _all_prompts(isc,"4.4.3.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "4.4.3.1")


# ---------------------------------------------------------------------------
# Depth 5
# ---------------------------------------------------------------------------


class TestDepth5:
    """Tests for depth-5 prompt generation."""

    def test_numeric_lists_full_hierarchy(self, isc):
        """Numeric prompt includes all ancestor subclauses."""
        prompt = _all_prompts(isc,
            "4.4.3.1.2", "~/LRM.pdf",
        )
        assert all(
            f"§{s}" in prompt
            for s in ["4.4", "4.4.3", "4.4.3.1"]
        )

    def test_annex_lists_full_hierarchy(self, isc):
        """Annex prompt includes all ancestor subclauses."""
        prompt = _all_prompts(isc,
            "A.7.5.3.1", "~/LRM.pdf",
        )
        assert all(
            f"§{s}" in prompt
            for s in ["A.7", "A.7.5", "A.7.5.3"]
        )

    def test_has_common_structure(self, isc):
        """Prompt has all common structure elements."""
        prompt = _all_prompts(isc,
            "4.4.3.1.2", "~/LRM.pdf",
        )
        assert not _check_common_structure(prompt, "4.4.3.1.2")


# ---------------------------------------------------------------------------
# Normative implementation discipline
# ---------------------------------------------------------------------------


class TestNormativeImplementation:
    """Tests that the prompt defines 'done' in positive terms."""

    def test_prompt_replaces_hard_stop_with_completion_statement(self, isc):
        """Hard stop is replaced with a positive completion statement."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "This step is complete when the file edits on disk"
            " land the step's deliverable."
        ) in prompt

    def test_prompt_defines_normative_statement_as_done(self, isc):
        """Constraints define when a normative statement is satisfied."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "A normative statement in §6.3 is satisfied when production"
            " code applies the rule and a test at the same pipeline stage"
            " observes the rule being applied by that production code."
        ) in prompt

    def test_prompt_anchors_stages_in_project_mapping(self, isc):
        """Constraints anchor pipeline stages in the project mapping."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "Pipeline stages come from the project's stage-to-file mapping"
        ) in prompt

    def test_prompt_permits_shared_file_edits_when_text_requires(self, isc):
        """Constraints permit shared-file edits the subclause text requires."""
        prompt = _all_prompts(isc, "6.3")
        assert "edit those shared files in this run" in prompt

    def test_prompt_separates_requirement_ownership_from_file_scope(
        self, isc,
    ):
        """Constraints separate requirement ownership from file scope."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "Requirement ownership is scoped by subclause; file editing"
            " is scoped by what §6.3's text requires."
        ) in prompt

    def test_prompt_requires_normative_enumeration(self, isc):
        """Functionality step requires enumerating normative statements."""
        prompt = _all_prompts(isc, "6.3")
        assert "list every normative statement in §6.3's LRM text" in prompt

    def test_prompt_requires_per_statement_stage_and_file(self, isc):
        """Functionality step pairs each statement with stage and file."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "name the pipeline stage the rule applies to and the source"
            " file that will carry the rule"
        ) in prompt

    def test_prompt_requires_production_code_applies_rule(self, isc):
        """Functionality step requires production code to apply each rule."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "make the source-file edits so the production code applies"
            " each rule"
        ) in prompt

    def test_prompt_tests_exercise_production_not_reference(self, isc):
        """Tests step requires observing production, not a reference."""
        prompt = _all_prompts(isc, "6.3")
        assert (
            "observe the rule being applied by production code, not by"
            " a reference model or helper"
        ) in prompt
