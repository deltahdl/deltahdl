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

    def test_exclude_note_forbids_all_actions(self, isc):
        """Exclude note forbids implement, move, delete, rename."""
        prompt = _all_prompts(isc, "6.3", exclude="6.3.1")
        for verb in ("implement", "move", "delete", "rename"):
            assert verb in prompt.lower()

    def test_exclude_note_says_leave_as_is(self, isc):
        """Exclude note tells Claude to leave descendant content as-is."""
        prompt = _all_prompts(isc, "6.3", exclude="6.3.1")
        assert "Leave it exactly as-is" in prompt

    def test_no_exclude_omits_off_limits(self, isc):
        """Without --exclude, OFF-LIMITS label does not appear."""
        prompt = _all_prompts(isc, "6.3")
        assert "OFF-LIMITS SUBCLAUSES" not in prompt

    def test_audit_scope_step_exists(self, isc):
        """An 'Auditing scope' step is present."""
        names = _step_names(isc, "6.3")
        assert "Auditing scope" in names

    def test_audit_scope_after_implementation(self, isc):
        """Auditing scope comes after Implementing missing functionality."""
        names = _step_names(isc, "6.3")
        impl_idx = names.index("Implementing missing functionality")
        audit_idx = names.index("Auditing scope")
        assert audit_idx == impl_idx + 1

    def test_audit_scope_before_summary(self, isc):
        """Auditing scope comes before Summarizing actions."""
        names = _step_names(isc, "6.3")
        audit_idx = names.index("Auditing scope")
        summary_idx = names.index("Summarizing actions")
        assert audit_idx == summary_idx - 1

    def test_audit_scope_mentions_git_diff(self, isc):
        """Audit step instructs to run git diff."""
        steps = isc.build_steps("6.3", "~/LRM.pdf")
        audit = next(p for n, p in steps if n == "Auditing scope")
        assert "git diff" in audit

    def test_audit_scope_mentions_revert(self, isc):
        """Audit step instructs to revert descendant changes."""
        steps = isc.build_steps("6.3", "~/LRM.pdf")
        audit = next(p for n, p in steps if n == "Auditing scope")
        assert "git checkout" in audit

    def test_audit_scope_includes_exclude_note(self, isc):
        """Audit step includes exclude note when exclude is provided."""
        steps = isc.build_steps("6.3", "~/LRM.pdf", exclude="6.3.1")
        audit = next(p for n, p in steps if n == "Auditing scope")
        assert "OFF-LIMITS SUBCLAUSES" in audit


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
