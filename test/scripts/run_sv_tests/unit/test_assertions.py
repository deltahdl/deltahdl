import ast
from types import ModuleType
from unittest.mock import patch

import pytest


def test_constant_true(rst: ModuleType) -> None:
    assert rst.eval_node(ast.Constant(value=True)) is True


def test_constant_integer(rst: ModuleType) -> None:
    assert rst.eval_node(ast.Constant(value=42)) == 42


def test_equality_pass(rst: ModuleType) -> None:
    tree = ast.parse("('hello' == 'hello')", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_equality_fail(rst: ModuleType) -> None:
    tree = ast.parse("(1 == 2)", mode="eval")
    assert rst.eval_node(tree.body) is False


def test_in_operator(rst: ModuleType) -> None:
    tree = ast.parse("('est' in 'Test')", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_not_in_operator(rst: ModuleType) -> None:
    tree = ast.parse("('xyz' not in 'Test')", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_bool_and(rst: ModuleType) -> None:
    tree = ast.parse("(True and True)", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_bool_or(rst: ModuleType) -> None:
    tree = ast.parse("(False or True)", mode="eval")
    assert rst.eval_node(tree.body) is True


def test_unary_not(rst: ModuleType) -> None:
    tree = ast.parse("(not False)", mode="eval")
    assert rst.eval_node(tree.body) is True


@pytest.mark.parametrize("expr", [
    "((1 << 32) + 2 == 4294967298)",
    "(7 - 2 == 5)",
    "(6 * 7 == 42)",
    "(7 // 2 == 3)",
    "(7 % 2 == 1)",
    "(2 ** 10 == 1024)",
    "(1024 >> 3 == 128)",
    "(6 & 3 == 2)",
    "(6 | 3 == 7)",
    "(6 ^ 3 == 5)",
])
def test_binary_operators(rst: ModuleType, expr: str) -> None:
    tree = ast.parse(expr, mode="eval")
    assert rst.eval_node(tree.body) is True


def test_the_suites_stream_concat_assertion_is_read_as_the_python_it_is(
    rst: ModuleType,
) -> None:
    line = ":assert: ((( 1094861636 << 32) +  1162233672) ==  4702394921427289928) \n"
    assert rst.check_assertions(line) == (True, "")


def test_unsupported_node_raises(rst: ModuleType) -> None:
    raised = False
    try:
        rst.eval_node(ast.Name(id="x"))
    except ValueError:
        raised = True
    assert raised


def _check_without_ast(rst: ModuleType, line: str) -> tuple[bool, str]:
    with patch("ast.parse", side_effect=SyntaxError):
        outcome: tuple[bool, str] = rst.check_assertions(line)
    return outcome


def test_passing_assertion(rst: ModuleType) -> None:
    assert rst.check_assertions(":assert: (True)") == (True, "")


def test_failing_assertion(rst: ModuleType) -> None:
    assert rst.check_assertions(":assert: (1 == 2)")[0] is False


def test_failing_assertion_names_the_failure(rst: ModuleType) -> None:
    assert "Assertion failed" in rst.check_assertions(":assert: (1 == 2)")[1]


def test_no_assertions_passes(rst: ModuleType) -> None:
    assert rst.check_assertions("hello world\n") == (True, "")


def test_multiple_assertions_all_pass(rst: ModuleType) -> None:
    stdout = ":assert: (True)\n:assert: (1 == 1)\n"
    assert rst.check_assertions(stdout) == (True, "")


def test_multiple_assertions_one_fails(rst: ModuleType) -> None:
    stdout = ":assert: (True)\n:assert: (1 == 2)\n"
    ok, _ = rst.check_assertions(stdout)
    assert ok is False


def test_a_nul_character_a_displayed_value_carries_is_no_part_of_the_expression(
    rst: ModuleType,
) -> None:
    stdout = ":assert: ('TEST' in 'Test\0\0\0TEST')\n:assert: ('Test' in 'Test\0TEST')\n"
    assert rst.check_assertions(stdout) == (True, "")


def test_a_comparison_over_nul_characters_reads_the_characters_around_them(
    rst: ModuleType,
) -> None:
    assert rst.check_assertions(":assert: ('ab' == 'a\0b')") == (True, "")


def test_a_comparison_over_nul_characters_still_fails_on_the_characters_around_them(
    rst: ModuleType,
) -> None:
    assert rst.check_assertions(":assert: ('ac' == 'a\0b')")[0] is False


def test_syntax_error_fails(rst: ModuleType) -> None:
    assert rst.check_assertions(":assert: (!!!)")[0] is False


def test_syntax_error_names_the_parse_failure(rst: ModuleType) -> None:
    assert "Assertion parse error" in rst.check_assertions(":assert: (!!!)")[1]


def test_string_equality_pass(rst: ModuleType) -> None:
    assert rst.try_string_equality("('hello' == 'hello')") is True


def test_string_equality_fail(rst: ModuleType) -> None:
    assert rst.try_string_equality("('hello' == 'world')") is False


def test_string_equality_fallback_pass(rst: ModuleType) -> None:
    assert _check_without_ast(rst, ":assert: ('same' == 'same')") == (True, "")


def test_string_equality_fallback_fail(rst: ModuleType) -> None:
    assert _check_without_ast(rst, ":assert: ('abc' == 'xyz')")[0] is False


def test_string_equality_fallback_names_the_failure(rst: ModuleType) -> None:
    detail = _check_without_ast(rst, ":assert: ('abc' == 'xyz')")[1]
    assert "Assertion failed" in detail
