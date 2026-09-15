from types import ModuleType


class TestReportedSubclauses:
    def test_lists_every_subclause_in_the_order_written(
        self, rst: ModuleType,
    ) -> None:
        stderr = (
            "a.sv:1:1: error: enum has an x assignment (§6.19)\n"
            "a.sv:2:1: error: bad randomize() call (§16.12.17)\n"
        )
        assert rst.reported_subclauses(stderr) == ["6.19", "16.12.17"]

    def test_lists_nothing_when_no_diagnostic_names_a_subclause(
        self, rst: ModuleType,
    ) -> None:
        stderr = "a.sv:1:1: error: cannot open include file 'x.svh'\n"
        assert rst.reported_subclauses(stderr) == []


class TestTaggedClause:
    def test_returns_the_first_tag_when_it_names_a_clause(
        self, rst: ModuleType,
    ) -> None:
        assert rst.tagged_clause({"tags": "6.19"}) == "6.19"

    def test_returns_nothing_when_the_file_carries_no_tag(
        self, rst: ModuleType,
    ) -> None:
        assert rst.tagged_clause({"name": "enum_xx_inv"}) == ""

    def test_returns_nothing_when_the_first_tag_names_no_clause(
        self, rst: ModuleType,
    ) -> None:
        assert rst.tagged_clause({"tags": "uvm-random uvm"}) == ""


class TestSubclauseIsWithin:
    def test_a_clause_contains_itself(self, rst: ModuleType) -> None:
        assert rst.subclause_is_within("6.19", "6.19") is True

    def test_a_clause_contains_a_deeper_subclause(self, rst: ModuleType) -> None:
        assert rst.subclause_is_within("16.12.17", "16.12") is True

    def test_a_clause_does_not_contain_a_longer_number(
        self, rst: ModuleType,
    ) -> None:
        assert rst.subclause_is_within("16.121", "16.12") is False

    def test_a_clause_does_not_contain_the_clause_above_it(
        self, rst: ModuleType,
    ) -> None:
        assert rst.subclause_is_within("16", "16.12") is False
