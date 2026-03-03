"""Unit tests for prompt generation across all clause depths."""

from implement_subclause import (
    build_prompt_v as build_v,
    build_prompt_v_w as build_v_w,
    build_prompt_v_w_x as build_v_w_x,
    build_prompt_v_w_x_y as build_v_w_x_y,
    build_prompt_v_w_x_y_z as build_v_w_x_y_z,
)


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
    if "test-driven development" not in prompt.lower() and "TDD" not in prompt:
        missing.append("TDD/test-driven development")
    if "not just parsing" not in prompt:
        missing.append("'not just parsing'")
    if f"Issue {issue}" not in prompt:
        missing.append(f"'Issue {issue}'")
    if subclause not in prompt:
        missing.append(f"subclause '{subclause}'")
    return missing


# ---------------------------------------------------------------------------
# Depth 1: prompt_v
# ---------------------------------------------------------------------------


class TestPromptV:
    """Tests for depth-1 prompt generation."""

    def test_numeric_includes_clause_title(self):
        """Numeric prompt includes clause number and title."""
        prompt = build_v("4", _TITLES, "~/LRM.txt", issue=6)
        assert "Clause 4" in prompt and "Scheduling semantics" in prompt

    def test_annex_includes_collection(self):
        """Annex prompt includes collection name and subject."""
        prompt = build_v("B", _TITLES, "~/LRM.txt", issue=44)
        assert "Annex B" in prompt and "Keywords" in prompt

    def test_numeric_has_common_structure(self):
        """Numeric prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v("4", _TITLES, "~/LRM.txt", issue=6)
        assert not _check_common_structure(prompt, "4", 6)

    def test_annex_has_common_structure(self):
        """Annex prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v("B", _TITLES, "~/LRM.txt", issue=44)
        assert not _check_common_structure(prompt, "B", 44)

    def test_uses_short_lrm_path(self):
        """Prompt embeds the short LRM path."""
        prompt = build_v("B", _TITLES, "~/LRM.txt", issue=44)
        assert "~/LRM.txt" in prompt


# ---------------------------------------------------------------------------
# Depth 2: prompt_v_w
# ---------------------------------------------------------------------------


class TestPromptVW:
    """Tests for depth-2 prompt generation."""

    def test_numeric_includes_clause_and_subclause(self):
        """Numeric prompt mentions both clause and subclause."""
        prompt = build_v_w("4.1", _TITLES, "~/LRM.txt", issue=6)
        assert "Clause 4" in prompt and "4.1" in prompt

    def test_annex_includes_collection_and_subclause(self):
        """Annex prompt mentions both collection and subclause."""
        prompt = build_v_w("A.8", _TITLES, "~/LRM.txt", issue=44)
        assert "Annex A" in prompt and "A.8" in prompt

    def test_numeric_has_common_structure(self):
        """Numeric prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v_w("4.1", _TITLES, "~/LRM.txt", issue=6)
        assert not _check_common_structure(prompt, "4.1", 6)

    def test_numeric_includes_auto_detected_general(self):
        """Auto-detected 'General' sibling appears in the prompt."""
        prompt = build_v_w("4.4", _TITLES, "~/LRM.txt", issue=6)
        assert "Thoroughly understand 4.1" in prompt

    def test_numeric_includes_auto_detected_overview(self):
        """Auto-detected 'Overview' sibling appears in the prompt."""
        prompt = build_v_w("4.4", _TITLES, "~/LRM.txt", issue=6)
        assert "Thoroughly understand 4.2" in prompt


# ---------------------------------------------------------------------------
# Depth 3: prompt_v_w_x
# ---------------------------------------------------------------------------


class TestPromptVWX:
    """Tests for depth-3 prompt generation."""

    def test_numeric_walks_hierarchy(self):
        """Numeric prompt includes clause, context, ancestor, subclause."""
        prompt = build_v_w_x("6.24.1", _TITLES, "~/LRM.txt", issue=8)
        assert all(
            s in prompt
            for s in ["Clause 6", "6.1", "6.24.1", "6.24"]
        )

    def test_annex_walks_hierarchy(self):
        """Annex prompt includes collection, ancestors, subclause."""
        prompt = build_v_w_x("A.8.1", _TITLES, "~/LRM.txt", issue=44)
        assert all(
            s in prompt for s in ["Annex A", "A.8", "A.8.1"]
        )

    def test_numeric_has_common_structure(self):
        """Numeric prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v_w_x("6.24.1", _TITLES, "~/LRM.txt", issue=8)
        assert not _check_common_structure(prompt, "6.24.1", 8)

    def test_annex_has_common_structure(self):
        """Annex prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v_w_x("A.8.1", _TITLES, "~/LRM.txt", issue=44)
        assert not _check_common_structure(prompt, "A.8.1", 44)

    def test_context_skips_ancestor_duplicate(self):
        """Context subclause already in ancestors is not duplicated."""
        prompt = build_v_w_x("6.1.1", _TITLES, "~/LRM.txt", issue=8)
        assert prompt.count("Thoroughly understand 6.1 per") == 1

    def test_supplementary_lines_included(self):
        """Supplementary lines appear in the prompt."""
        prompt = build_v_w_x(
            "6.24.1", _TITLES, "~/LRM.txt", issue=8,
            supplementary="- Acknowledge Table 6-1\n",
        )
        assert "Table 6-1" in prompt


# ---------------------------------------------------------------------------
# Depth 4: prompt_v_w_x_y
# ---------------------------------------------------------------------------


class TestPromptVWXY:
    """Tests for depth-4 prompt generation."""

    def test_numeric_walks_full_hierarchy(self):
        """Numeric prompt includes clause, context, ancestors, subclause."""
        prompt = build_v_w_x_y("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        assert all(
            s in prompt
            for s in ["Clause 4", "4.1", "4.4", "4.4.3", "4.4.3.1"]
        )

    def test_annex_walks_full_hierarchy(self):
        """Annex prompt includes collection, ancestors, subclause."""
        prompt = build_v_w_x_y("A.7.5.3", _TITLES, "~/LRM.txt", issue=44)
        assert all(
            s in prompt
            for s in ["Annex A", "A.7", "A.7.5", "A.7.5.3"]
        )

    def test_numeric_hierarchy_order(self):
        """'Understand' steps appear in top-down order."""
        prompt = build_v_w_x_y("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        i_clause = prompt.index("Clause 4")
        i_context = prompt.index("4.1")
        i_parent = prompt.index("4.4")
        i_ref = prompt.index("4.4.3")
        i_sub = prompt.index("4.4.3.1")
        assert i_clause < i_context < i_parent < i_ref < i_sub

    def test_has_common_structure(self):
        """Prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v_w_x_y("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        assert not _check_common_structure(prompt, "4.4.3.1", 6)


# ---------------------------------------------------------------------------
# Depth 5: prompt_v_w_x_y_z
# ---------------------------------------------------------------------------


class TestPromptVWXYZ:
    """Tests for depth-5 prompt generation."""

    def test_numeric_walks_full_hierarchy(self):
        """Numeric prompt includes all hierarchy levels."""
        prompt = build_v_w_x_y_z(
            "4.4.3.1.2", _TITLES, "~/LRM.txt", issue=6,
        )
        assert all(
            s in prompt
            for s in [
                "Clause 4", "4.1", "4.4", "4.4.3", "4.4.3.1", "4.4.3.1.2",
            ]
        )

    def test_annex_walks_full_hierarchy(self):
        """Annex prompt includes all hierarchy levels."""
        prompt = build_v_w_x_y_z(
            "A.7.5.3.1", _TITLES, "~/LRM.txt", issue=44,
        )
        assert all(
            s in prompt
            for s in ["Annex A", "A.7", "A.7.5", "A.7.5.3", "A.7.5.3.1"]
        )

    def test_has_common_structure(self):
        """Prompt has TDD, 'not just parsing', issue, subclause."""
        prompt = build_v_w_x_y_z(
            "4.4.3.1.2", _TITLES, "~/LRM.txt", issue=6,
        )
        assert not _check_common_structure(prompt, "4.4.3.1.2", 6)
