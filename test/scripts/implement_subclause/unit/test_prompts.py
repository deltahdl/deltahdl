"""Unit tests for prompt generation across all clause depths."""


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _check_common_structure(prompt, subclause):
    """Return list of missing common structure elements."""
    missing = []
    if "failing unit test" not in prompt:
        missing.append("TDD (failing unit test)")
    if "test-driven development" not in prompt:
        missing.append("explicit TDD")
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
        prompt = isc.build_prompt("4", "~/LRM.pdf")
        assert "§4" in prompt

    def test_annex_includes_subclause(self, isc):
        """Annex prompt includes the target subclause."""
        prompt = isc.build_prompt("B", "~/LRM.pdf")
        assert "§B" in prompt

    def test_numeric_has_common_structure(self, isc):
        """Numeric prompt has all common structure elements."""
        prompt = isc.build_prompt("4", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "4")

    def test_annex_has_common_structure(self, isc):
        """Annex prompt has all common structure elements."""
        prompt = isc.build_prompt("B", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "B")

    def test_uses_short_lrm_path(self, isc):
        """Prompt embeds the short LRM path."""
        prompt = isc.build_prompt("B", "~/LRM.pdf")
        assert "~/LRM.pdf" in prompt

    def test_depth_1_mentions_general_overview(self, isc):
        """Depth-1 prompt instructs Claude to read General/Overview."""
        prompt = isc.build_prompt("4", "~/LRM.pdf")
        assert "General" in prompt or "Overview" in prompt


# ---------------------------------------------------------------------------
# Depth 2
# ---------------------------------------------------------------------------


class TestDepth2:
    """Tests for depth-2 prompt generation."""

    def test_numeric_has_common_structure(self, isc):
        """Numeric prompt has all common structure elements."""
        prompt = isc.build_prompt("4.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "4.1")

    def test_depth_2_mentions_general_overview(self, isc):
        """Depth-2 prompt instructs Claude to read General/Overview."""
        prompt = isc.build_prompt("4.4", "~/LRM.pdf")
        assert "General" in prompt


# ---------------------------------------------------------------------------
# Depth 3
# ---------------------------------------------------------------------------


class TestDepth3:
    """Tests for depth-3 prompt generation."""

    def test_numeric_lists_ancestors(self, isc):
        """Numeric prompt lists ancestor subclauses."""
        prompt = isc.build_prompt("6.24.1", "~/LRM.pdf")
        assert "§6.24" in prompt

    def test_annex_lists_ancestors(self, isc):
        """Annex prompt lists ancestor subclauses."""
        prompt = isc.build_prompt("A.8.1", "~/LRM.pdf")
        assert "§A.8" in prompt

    def test_numeric_has_common_structure(self, isc):
        """Numeric prompt has all common structure elements."""
        prompt = isc.build_prompt("6.24.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "6.24.1")

    def test_annex_has_common_structure(self, isc):
        """Annex prompt has all common structure elements."""
        prompt = isc.build_prompt("A.8.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "A.8.1")


# ---------------------------------------------------------------------------
# Depth 4
# ---------------------------------------------------------------------------


class TestDepth4:
    """Tests for depth-4 prompt generation."""

    def test_numeric_lists_full_hierarchy(self, isc):
        """Numeric prompt lists all ancestor subclauses."""
        prompt = isc.build_prompt("4.4.3.1", "~/LRM.pdf")
        assert all(
            f"§{s}" in prompt
            for s in ["4.4", "4.4.3"]
        )

    def test_annex_lists_full_hierarchy(self, isc):
        """Annex prompt lists all ancestor subclauses."""
        prompt = isc.build_prompt("A.7.5.3", "~/LRM.pdf")
        assert all(
            f"§{s}" in prompt
            for s in ["A.7", "A.7.5"]
        )

    def test_has_common_structure(self, isc):
        """Prompt has all common structure elements."""
        prompt = isc.build_prompt("4.4.3.1", "~/LRM.pdf")
        assert not _check_common_structure(prompt, "4.4.3.1")


# ---------------------------------------------------------------------------
# Depth 5
# ---------------------------------------------------------------------------


class TestDepth5:
    """Tests for depth-5 prompt generation."""

    def test_numeric_lists_full_hierarchy(self, isc):
        """Numeric prompt includes all ancestor subclauses."""
        prompt = isc.build_prompt(
            "4.4.3.1.2", "~/LRM.pdf",
        )
        assert all(
            f"§{s}" in prompt
            for s in ["4.4", "4.4.3", "4.4.3.1"]
        )

    def test_annex_lists_full_hierarchy(self, isc):
        """Annex prompt includes all ancestor subclauses."""
        prompt = isc.build_prompt(
            "A.7.5.3.1", "~/LRM.pdf",
        )
        assert all(
            f"§{s}" in prompt
            for s in ["A.7", "A.7.5", "A.7.5.3"]
        )

    def test_has_common_structure(self, isc):
        """Prompt has all common structure elements."""
        prompt = isc.build_prompt(
            "4.4.3.1.2", "~/LRM.pdf",
        )
        assert not _check_common_structure(prompt, "4.4.3.1.2")
