from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

_SIGNED_INT_BESIDE_UNSIGNED_LITERAL = (
    "((-1515870811 == 2779096485) and ( 1515870810 == 1515870810))"
)


def _simulate_the_multidim_array_file(
    rst: ModuleType, tmp_path: Path, returncode: int, assertion: str,
) -> tuple[dict[str, Any], int]:
    sv = tmp_path / "chapter-7" / "arrays" / "unpacked" / "unpacked_multidim_array.sv"
    sv.parent.mkdir(parents=True)
    sv.write_text(
        "/*\n:name: unpacked_multidim_array\n"
        ":type: simulation elaboration parsing\n:tags: 7.4\n*/\n"
        "module top; endmodule\n"
    )
    mock_result = MagicMock(
        returncode=returncode, stdout=f":assert: {assertion}\n", stderr="",
    )
    with patch.object(rst.subprocess, "run", return_value=mock_result):
        evaluated: tuple[dict[str, Any], int] = rst.build_result(str(sv))
        return evaluated


def test_a_file_printing_the_false_assertion_the_standard_gives_evaluates_as_a_pass(
    rst: ModuleType, tmp_path: Path,
) -> None:
    result, ok = _simulate_the_multidim_array_file(
        rst, tmp_path, 0, _SIGNED_INT_BESIDE_UNSIGNED_LITERAL,
    )
    assert (ok, result["status"]) == (1, "pass")


def test_a_file_printing_the_true_assertion_the_suite_expects_evaluates_as_a_fail(
    rst: ModuleType, tmp_path: Path,
) -> None:
    result, ok = _simulate_the_multidim_array_file(
        rst, tmp_path, 0,
        "(( 2779096485 == 2779096485) and ( 1515870810 == 1515870810))",
    )
    assert (ok, result["status"]) == (0, "fail")


def test_a_file_whose_simulation_fails_evaluates_as_a_fail(
    rst: ModuleType, tmp_path: Path,
) -> None:
    result, ok = _simulate_the_multidim_array_file(
        rst, tmp_path, 1, _SIGNED_INT_BESIDE_UNSIGNED_LITERAL,
    )
    assert (ok, result["status"]) == (0, "fail")


def test_a_file_printing_the_false_assertion_is_not_an_expected_rejection(
    rst: ModuleType, tmp_path: Path,
) -> None:
    result, _ = _simulate_the_multidim_array_file(
        rst, tmp_path, 0, _SIGNED_INT_BESIDE_UNSIGNED_LITERAL,
    )
    assert result["should_fail"] is False
