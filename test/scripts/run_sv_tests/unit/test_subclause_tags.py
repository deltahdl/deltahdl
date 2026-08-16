"""Unit tests for reading a subclause out of a diagnostic and out of the corpus.

Every file in the sv-tests corpus records the clause it exercises in a
``:tags:`` field, and every deltahdl diagnostic that enforces a rule of
IEEE 1800-2023 names the subclause it enforces. The three functions covered
here read those two numbers and decide whether one is under the other.
"""

from types import ModuleType


class TestReportedSubclauses:
    """Tests for the reported_subclauses() function."""

    def test_lists_every_subclause_in_the_order_written(
        self, rst: ModuleType,
    ) -> None:
        """reported_subclauses() should list what the diagnostics named.

        DiagEngine::Emit in src/common/diagnostic.cpp appends the subclause of
        IEEE 1800-2023 a diagnostic enforces to its message, as (§11.4.14).
        """
        stderr = (
            "a.sv:1:1: error: enum has an x assignment (§6.19)\n"
            "a.sv:2:1: error: bad randomize() call (§16.12.17)\n"
        )
        assert rst.reported_subclauses(stderr) == ["6.19", "16.12.17"]

    def test_lists_nothing_when_no_diagnostic_names_a_subclause(
        self, rst: ModuleType,
    ) -> None:
        """A report built with Subclause::None() enforces no rule of the standard.

        Subclause::None in src/common/diagnostic.h reserves it for a fact about
        the run, such as a file that cannot be opened, and 26 sites under src/
        use it.
        """
        stderr = "a.sv:1:1: error: cannot open include file 'x.svh'\n"
        assert rst.reported_subclauses(stderr) == []


class TestTaggedClause:
    """Tests for the tagged_clause() function."""

    def test_returns_the_first_tag_when_it_names_a_clause(
        self, rst: ModuleType,
    ) -> None:
        """The first :tags: entry is the clause the corpus says a file exercises."""
        assert rst.tagged_clause({"tags": "6.19"}) == "6.19"

    def test_returns_nothing_when_the_file_carries_no_tag(
        self, rst: ModuleType,
    ) -> None:
        """A file with no :tags: field names no clause to check a rejection against."""
        assert rst.tagged_clause({"name": "enum_xx_inv"}) == ""

    def test_returns_nothing_when_the_first_tag_names_no_clause(
        self, rst: ModuleType,
    ) -> None:
        """A tag that is not a clause number is not a clause number.

        Three corpus files marked should_fail_because tag ``uvm-random uvm``,
        and reading ``uvm-random`` as a clause would compare a rejection
        against a clause of IEEE 1800-2023 that does not exist.
        """
        assert rst.tagged_clause({"tags": "uvm-random uvm"}) == ""


class TestSubclauseIsWithin:
    """Tests for the subclause_is_within() function."""

    def test_a_clause_contains_itself(self, rst: ModuleType) -> None:
        """A diagnostic naming the tagged clause enforces a rule under it."""
        assert rst.subclause_is_within("6.19", "6.19") is True

    def test_a_clause_contains_a_deeper_subclause(self, rst: ModuleType) -> None:
        """A file tagged with a clause exercises the subclauses under it.

        Half the tagged corpus files name a clause two levels deep, and a
        diagnostic is free to name something deeper than the tag.
        """
        assert rst.subclause_is_within("16.12.17", "16.12") is True

    def test_a_clause_does_not_contain_a_longer_number(
        self, rst: ModuleType,
    ) -> None:
        """§16.121 is not under §16.12, though the text of one starts the other.

        Comparing the two as strings makes §16.12 a prefix of §16.121, so
        every diagnostic enforcing §16.121 would score the pass a file tagged
        §16.12 was written for.
        """
        assert rst.subclause_is_within("16.121", "16.12") is False

    def test_a_clause_does_not_contain_the_clause_above_it(
        self, rst: ModuleType,
    ) -> None:
        """A diagnostic naming §16 says nothing about the rules under §16.12."""
        assert rst.subclause_is_within("16", "16.12") is False
