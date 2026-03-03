"""Unit tests for prompt generation across all clause depths."""

from implement_subclause import build_prompt


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_TITLES = {
    "3": "Design and verification building blocks",
    "4": "Scheduling semantics",
    "4.1": "General",
    "4.2": "Overview",
    "4.4": "Stratified event scheduler",
    "4.4.3": "The PLI callback control points",
    "4.4.3.1": "Preponed PLI region",
    "6": "Data types",
    "6.1": "General",
    "6.24": "String data type",
    "6.24.1": "String operators",
    "A": "(normative) Formal syntax",
    "A.7": "Specify section",
    "A.7.5": "System timing check commands",
    "A.7.5.3": "System timing check event definitions",
    "A.8": "Expressions",
    "A.8.1": "Concatenations",
    "B": "(normative) Keywords",
}


def _check_common_structure(prompt, subclause, issue):
    """Return list of missing common structure elements."""
    missing = []
    if "failing unit test" not in prompt:
        missing.append("TDD (failing unit test)")
    if "test-driven development" not in prompt:
        missing.append("explicit TDD")
    if "pipeline stages" not in prompt:
        missing.append("'pipeline stages'")
    if f"Issue #{issue}" not in prompt:
        missing.append(f"'Issue #{issue}'")
    if f"§{subclause}" not in prompt:
        missing.append(f"subclause '§{subclause}'")
    if "LRM prose" not in prompt:
        missing.append("copyright constraint")
    return missing


# ---------------------------------------------------------------------------
# Depth 1
# ---------------------------------------------------------------------------


class TestDepth1:
    """Tests for depth-1 prompt generation."""

    def test_numeric_includes_subclause(self):
        """Numeric prompt includes the target subclause."""
        prompt = build_prompt("4", _TITLES, "~/LRM.txt", issue=6)
        assert "§4" in prompt

    def test_annex_includes_subclause(self):
        """Annex prompt includes the target subclause."""
        prompt = build_prompt("B", _TITLES, "~/LRM.txt", issue=44)
        assert "§B" in prompt

    def test_numeric_has_common_structure(self):
        """Numeric prompt has all common structure elements."""
        prompt = build_prompt("4", _TITLES, "~/LRM.txt", issue=6)
        assert not _check_common_structure(prompt, "4", 6)

    def test_annex_has_common_structure(self):
        """Annex prompt has all common structure elements."""
        prompt = build_prompt("B", _TITLES, "~/LRM.txt", issue=44)
        assert not _check_common_structure(prompt, "B", 44)

    def test_uses_short_lrm_path(self):
        """Prompt embeds the short LRM path."""
        prompt = build_prompt("B", _TITLES, "~/LRM.txt", issue=44)
        assert "~/LRM.txt" in prompt

    def test_depth_1_reads_only_target(self):
        """Depth-1 prompt reads only the target subclause, no ancestors."""
        prompt = build_prompt("4", _TITLES, "~/LRM.txt", issue=6)
        assert "Read §4 for context." in prompt


# ---------------------------------------------------------------------------
# Depth 2
# ---------------------------------------------------------------------------


class TestDepth2:
    """Tests for depth-2 prompt generation."""

    def test_numeric_no_top_level_in_context(self):
        """Numeric prompt does not list top-level clause in context."""
        prompt = build_prompt("4.1", _TITLES, "~/LRM.txt", issue=6)
        assert "related subclauses (§4.2)" in prompt

    def test_annex_no_top_level_in_context(self):
        """Annex prompt does not list top-level annex in context."""
        prompt = build_prompt("A.8", _TITLES, "~/LRM.txt", issue=44)
        assert "Read §A.8 for context." in prompt

    def test_numeric_has_common_structure(self):
        """Numeric prompt has all common structure elements."""
        prompt = build_prompt("4.1", _TITLES, "~/LRM.txt", issue=6)
        assert not _check_common_structure(prompt, "4.1", 6)

    def test_numeric_includes_auto_detected_general(self):
        """Auto-detected 'General' sibling appears in the prompt."""
        prompt = build_prompt("4.4", _TITLES, "~/LRM.txt", issue=6)
        assert "§4.1" in prompt

    def test_numeric_includes_auto_detected_overview(self):
        """Auto-detected 'Overview' sibling appears in the prompt."""
        prompt = build_prompt("4.4", _TITLES, "~/LRM.txt", issue=6)
        assert "§4.2" in prompt


# ---------------------------------------------------------------------------
# Depth 3
# ---------------------------------------------------------------------------


class TestDepth3:
    """Tests for depth-3 prompt generation."""

    def test_numeric_lists_related_subclauses(self):
        """Numeric prompt lists context and ancestor subclauses."""
        prompt = build_prompt("6.24.1", _TITLES, "~/LRM.txt", issue=8)
        assert all(
            f"§{s}" in prompt
            for s in ["6.1", "6.24", "6.24.1"]
        )

    def test_annex_lists_related_subclauses(self):
        """Annex prompt lists ancestor subclauses."""
        prompt = build_prompt("A.8.1", _TITLES, "~/LRM.txt", issue=44)
        assert all(
            f"§{s}" in prompt for s in ["A.8", "A.8.1"]
        )

    def test_numeric_has_common_structure(self):
        """Numeric prompt has all common structure elements."""
        prompt = build_prompt("6.24.1", _TITLES, "~/LRM.txt", issue=8)
        assert not _check_common_structure(prompt, "6.24.1", 8)

    def test_annex_has_common_structure(self):
        """Annex prompt has all common structure elements."""
        prompt = build_prompt("A.8.1", _TITLES, "~/LRM.txt", issue=44)
        assert not _check_common_structure(prompt, "A.8.1", 44)

    def test_context_skips_ancestor_duplicate(self):
        """Context subclause already in ancestors is not duplicated."""
        prompt = build_prompt("6.1.1", _TITLES, "~/LRM.txt", issue=8)
        assert prompt.count("§6.1") == prompt.count("§6.1.1") + 1

    def test_supplementary_lines_included(self):
        """Supplementary lines appear in the prompt."""
        prompt = build_prompt(
            "6.24.1", _TITLES, "~/LRM.txt", issue=8,
            supplementary="Consult Table 6-1 at /t (Markdown)"
            " when implementing.",
        )
        assert "Table 6-1" in prompt


# ---------------------------------------------------------------------------
# Depth 4
# ---------------------------------------------------------------------------


class TestDepth4:
    """Tests for depth-4 prompt generation."""

    def test_numeric_lists_full_hierarchy(self):
        """Numeric prompt lists context and all ancestor subclauses."""
        prompt = build_prompt("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        assert all(
            f"§{s}" in prompt
            for s in ["4.1", "4.4", "4.4.3", "4.4.3.1"]
        )

    def test_annex_lists_full_hierarchy(self):
        """Annex prompt lists all ancestor subclauses."""
        prompt = build_prompt("A.7.5.3", _TITLES, "~/LRM.txt", issue=44)
        assert all(
            f"§{s}" in prompt
            for s in ["A.7", "A.7.5", "A.7.5.3"]
        )

    def test_numeric_subclause_order(self):
        """Related subclauses appear in top-down order."""
        prompt = build_prompt("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        start = prompt.index("(") + 1
        end = prompt.index(")")
        refs = [s.strip() for s in prompt[start:end].split(",")]
        assert refs == ["§4.1", "§4.2", "§4.4", "§4.4.3"]

    def test_has_common_structure(self):
        """Prompt has all common structure elements."""
        prompt = build_prompt("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        assert not _check_common_structure(prompt, "4.4.3.1", 6)


# ---------------------------------------------------------------------------
# Depth 5
# ---------------------------------------------------------------------------


class TestDepth5:
    """Tests for depth-5 prompt generation."""

    def test_numeric_lists_full_hierarchy(self):
        """Numeric prompt includes all ancestor and context subclauses."""
        prompt = build_prompt(
            "4.4.3.1.2", _TITLES, "~/LRM.txt", issue=6,
        )
        assert all(
            f"§{s}" in prompt
            for s in [
                "4.1", "4.4", "4.4.3", "4.4.3.1", "4.4.3.1.2",
            ]
        )

    def test_annex_lists_full_hierarchy(self):
        """Annex prompt includes all ancestor subclauses."""
        prompt = build_prompt(
            "A.7.5.3.1", _TITLES, "~/LRM.txt", issue=44,
        )
        assert all(
            f"§{s}" in prompt
            for s in ["A.7", "A.7.5", "A.7.5.3", "A.7.5.3.1"]
        )

    def test_has_common_structure(self):
        """Prompt has all common structure elements."""
        prompt = build_prompt(
            "4.4.3.1.2", _TITLES, "~/LRM.txt", issue=6,
        )
        assert not _check_common_structure(prompt, "4.4.3.1.2", 6)
