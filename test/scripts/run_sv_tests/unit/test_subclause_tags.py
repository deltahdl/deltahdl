from types import ModuleType

import pytest


def test_returns_the_first_tag_when_it_names_a_clause(rst: ModuleType) -> None:
    assert rst.tagged_clause({"tags": "6.19"}, "enum_xx_inv.sv") == "6.19"


def test_returns_nothing_when_the_file_carries_no_tag_and_no_clause_prefix(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"name": "enum_xx_inv"}, "enum_xx_inv.sv") == ""


def test_returns_nothing_when_the_first_tag_names_no_clause_and_the_name_no_prefix(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "uvm-random uvm"}, "randomize_5.sv") == ""


def test_returns_the_file_name_prefix_when_the_first_tag_names_no_clause(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause(
        {"tags": "uvm-random uvm"},
        "18.6.3--behavior-of-randomization-methods_5.sv",
    ) == "18.6.3"


def test_returns_the_first_tag_over_a_different_file_name_prefix(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "6.19"}, "7.3--net_types_1.sv") == "6.19"


def test_returns_nothing_for_a_number_the_name_does_not_close_with_two_dashes(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "uvm"}, "18.6.3-randomize.sv") == ""


def test_a_tag_the_suite_numbers_as_1800_2017_does_names_the_1800_2023_subclause(
    rst: ModuleType,
) -> None:
    assert rst.subclause_of_tag("18.5.10") == "18.5.9"


def test_a_tag_below_a_renumbered_subclause_is_renumbered_with_it(
    rst: ModuleType,
) -> None:
    assert rst.subclause_of_tag("18.5.14.1") == "18.5.13.1"


def test_a_tag_of_a_subclause_moved_to_another_clause_names_its_new_home(
    rst: ModuleType,
) -> None:
    assert rst.subclause_of_tag("18.5.3") == "11.4.13"


def test_a_tag_the_two_editions_number_alike_is_kept(rst: ModuleType) -> None:
    assert rst.subclause_of_tag("6.19") == "6.19"


def test_a_tag_that_disagrees_with_its_own_file_rather_than_the_edition_is_kept(
    rst: ModuleType,
) -> None:
    assert rst.subclause_of_tag("18.8") == "18.8"


def test_a_file_the_suite_tags_on_an_exception_is_judged_by_the_rule_it_tests(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "13.4.4"}, "13.4.4--fork-invalid.sv") == "13.4"


def test_a_file_of_the_same_tag_outside_the_table_keeps_its_tag(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "13.4.4"}, "13.4.4--fork-valid.sv") == "13.4.4"


@pytest.mark.parametrize("name, tag, rule", [
    ("variable-slice-zero.sv", "7.4.3", "11.5.1"),
    ("14.3--clocking-block-signals-error.sv", "14.3", "10.4"),
    ("11.4.14.3--unpack_stream_inv.sv", "11.4.14.3", "11.4.14"),
])
def test_a_file_tagged_by_the_feature_it_uses_is_judged_by_the_rule_it_breaks(
    rst: ModuleType, name: str, tag: str, rule: str,
) -> None:
    assert rst.tagged_clause({"tags": tag}, name) == rule


def test_a_file_the_suite_expects_accepted_is_judged_by_the_rule_it_breaks(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "20.4"}, "20.4--timeformat.sv") == "20.4.3"


def test_a_file_the_suite_tags_on_the_next_subclause_is_judged_by_the_rule_it_tests(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause({"tags": "9.3.3"}, "9.3.3--fork_return.sv") == "9.3.2"


def test_a_file_the_suite_tags_on_the_clause_it_was_split_out_of_is_judged_by_the_rule_it_tests(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause(
        {"tags": "10.3"}, "10.3--proc-assignment--bad.sv",
    ) == "10.4"


def test_a_file_the_suite_tags_one_subclause_off_is_judged_by_the_rule_it_tests(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause(
        {"tags": "18.8"}, "18.9--controlling-constraints-with-constraint_mode_1.sv",
    ) == "18.9"


def test_a_file_the_suite_tags_on_its_parent_test_is_judged_by_the_rule_it_tests(
    rst: ModuleType,
) -> None:
    assert rst.tagged_clause(
        {"tags": "18.17.6"},
        "18.17.6--aborting-productions-break-and-return_2_fail.sv",
    ) == "18.17"


@pytest.mark.parametrize("name, tag", [
    ("18.17.2--if-else-production-statements_0_fail.sv", "18.17.2"),
    ("18.17.2--if-else-production-statements_2_fail.sv", "18.17.2"),
    ("18.17.3--case-production-statements_0_fail.sv", "18.17.3"),
])
def test_a_file_tagged_on_the_construct_its_undeclared_name_stands_in_is_judged_by_the_name_rule(
    rst: ModuleType, name: str, tag: str,
) -> None:
    assert rst.tagged_clause({"tags": tag}, name) == "23.9"
