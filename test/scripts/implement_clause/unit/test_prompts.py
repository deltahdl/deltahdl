"""Unit tests for prompt generation across all clause depths."""

import pytest

from implement_clause.prompt_v import build_prompt as build_v
from implement_clause.prompt_v_w import build_prompt as build_v_w
from implement_clause.prompt_v_w_x import build_prompt as build_v_w_x
from implement_clause.prompt_v_w_x_y import build_prompt as build_v_w_x_y
from implement_clause.prompt_v_w_x_y_z import build_prompt as build_v_w_x_y_z


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_TITLES = {
    "3": "Design and verification building blocks",
    "4": "Scheduling semantics",
    "4.1": "General",
    "4.4": "Stratified event scheduler",
    "4.4.3": "The PLI callback control points",
    "4.4.3.1": "Preponed PLI region",
    "6": "Data types",
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


def _assert_common_structure(prompt, subclause, issue):
    """Assert that the prompt has the standard implementation/prove/issue structure."""
    assert "test-driven development" in prompt.lower() or "TDD" in prompt
    assert "not just parsing" in prompt
    assert f"Issue {issue}" in prompt
    assert subclause in prompt


# ---------------------------------------------------------------------------
# Depth 1: prompt_v
# ---------------------------------------------------------------------------


class TestPromptV:
    """Tests for depth-1 prompt generation."""

    def test_numeric_includes_clause_title(self):
        prompt = build_v("4", _TITLES, "~/LRM.txt", issue=6)
        assert "Clause 4" in prompt
        assert "Scheduling semantics" in prompt

    def test_annex_includes_collection(self):
        prompt = build_v("B", _TITLES, "~/LRM.txt", issue=44)
        assert "Annex B" in prompt
        assert "Keywords" in prompt

    def test_numeric_has_common_structure(self):
        prompt = build_v("4", _TITLES, "~/LRM.txt", issue=6)
        _assert_common_structure(prompt, "4", 6)

    def test_annex_has_common_structure(self):
        prompt = build_v("B", _TITLES, "~/LRM.txt", issue=44)
        _assert_common_structure(prompt, "B", 44)

    def test_uses_short_lrm_path(self):
        prompt = build_v("B", _TITLES, "~/LRM.txt", issue=44)
        assert "~/LRM.txt" in prompt


# ---------------------------------------------------------------------------
# Depth 2: prompt_v_w
# ---------------------------------------------------------------------------


class TestPromptVW:
    """Tests for depth-2 prompt generation."""

    def test_numeric_includes_clause_and_subclause(self):
        prompt = build_v_w("4.1", _TITLES, "~/LRM.txt", issue=6)
        assert "Clause 4" in prompt
        assert "4.1" in prompt

    def test_annex_includes_collection_and_subclause(self):
        prompt = build_v_w("A.8", _TITLES, "~/LRM.txt", issue=44)
        assert "Annex A" in prompt
        assert "A.8" in prompt

    def test_numeric_has_common_structure(self):
        prompt = build_v_w("4.1", _TITLES, "~/LRM.txt", issue=6)
        _assert_common_structure(prompt, "4.1", 6)


# ---------------------------------------------------------------------------
# Depth 3: prompt_v_w_x
# ---------------------------------------------------------------------------


class TestPromptVWX:
    """Tests for depth-3 prompt generation."""

    def test_numeric_walks_hierarchy(self):
        prompt = build_v_w_x("6.24.1", _TITLES, "~/LRM.txt", issue=8)
        assert "Clause 6" in prompt
        assert "6.1" in prompt
        # subclause fits within ancestor
        assert "6.24.1" in prompt
        assert "6.24" in prompt

    def test_annex_walks_hierarchy(self):
        prompt = build_v_w_x("A.8.1", _TITLES, "~/LRM.txt", issue=44)
        assert "Annex A" in prompt
        assert "A.8" in prompt
        assert "A.8.1" in prompt

    def test_numeric_has_common_structure(self):
        prompt = build_v_w_x("6.24.1", _TITLES, "~/LRM.txt", issue=8)
        _assert_common_structure(prompt, "6.24.1", 8)

    def test_annex_has_common_structure(self):
        prompt = build_v_w_x("A.8.1", _TITLES, "~/LRM.txt", issue=44)
        _assert_common_structure(prompt, "A.8.1", 44)

    def test_supplementary_lines_included(self):
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
        prompt = build_v_w_x_y("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        assert "Clause 4" in prompt
        assert "4.1" in prompt
        assert "4.4" in prompt
        assert "4.4.3" in prompt
        assert "4.4.3.1" in prompt

    def test_annex_walks_full_hierarchy(self):
        prompt = build_v_w_x_y("A.7.5.3", _TITLES, "~/LRM.txt", issue=44)
        assert "Annex A" in prompt
        assert "A.7" in prompt
        assert "A.7.5" in prompt
        assert "A.7.5.3" in prompt

    def test_numeric_hierarchy_order(self):
        """'Understand' steps appear in top-down order."""
        prompt = build_v_w_x_y("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        i_clause = prompt.index("Clause 4")
        i_principle = prompt.index("4.1")
        i_parent = prompt.index("4.4")
        i_ref = prompt.index("4.4.3")
        i_sub = prompt.index("4.4.3.1")
        assert i_clause < i_principle < i_parent < i_ref < i_sub

    def test_has_common_structure(self):
        prompt = build_v_w_x_y("4.4.3.1", _TITLES, "~/LRM.txt", issue=6)
        _assert_common_structure(prompt, "4.4.3.1", 6)


# ---------------------------------------------------------------------------
# Depth 5: prompt_v_w_x_y_z
# ---------------------------------------------------------------------------


class TestPromptVWXYZ:
    """Tests for depth-5 prompt generation."""

    def test_numeric_walks_full_hierarchy(self):
        prompt = build_v_w_x_y_z(
            "4.4.3.1.2", _TITLES, "~/LRM.txt", issue=6,
        )
        assert "Clause 4" in prompt
        assert "4.1" in prompt
        assert "4.4" in prompt
        assert "4.4.3" in prompt
        assert "4.4.3.1" in prompt
        assert "4.4.3.1.2" in prompt

    def test_annex_walks_full_hierarchy(self):
        prompt = build_v_w_x_y_z(
            "A.7.5.3.1", _TITLES, "~/LRM.txt", issue=44,
        )
        assert "Annex A" in prompt
        assert "A.7" in prompt
        assert "A.7.5" in prompt
        assert "A.7.5.3" in prompt
        assert "A.7.5.3.1" in prompt

    def test_has_common_structure(self):
        prompt = build_v_w_x_y_z(
            "4.4.3.1.2", _TITLES, "~/LRM.txt", issue=6,
        )
        _assert_common_structure(prompt, "4.4.3.1.2", 6)
