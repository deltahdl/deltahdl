import re
from unittest.mock import patch

import pytest

from lib.python import run_tests_common


def _printed_table(
    failed_by_clause: dict[str, int], capsys: pytest.CaptureFixture[str],
) -> str:
    run_tests_common.print_clause_breakdown(failed_by_clause)
    return re.sub(r"\033\[[0-9;]*m", "", capsys.readouterr().out)


def _cells(table: str, clause: str) -> list[str]:
    row = next(ln for ln in table.splitlines() if ln.startswith(f"│ {clause} "))
    return [c.strip() for c in row.strip("│").split("│")]


def test_natural_sort_key_orders_numbers_by_value() -> None:
    clauses = ["25", "5", "8.10", "8.9"]
    ordered = sorted(clauses, key=run_tests_common.natural_sort_key)
    assert ordered == ["5", "8.9", "8.10", "25"]


def test_the_table_is_drawn_in_boxes_under_its_two_headers(
    capsys: pytest.CaptureFixture[str],
) -> None:
    table = _printed_table({"5": 0}, capsys)
    assert all(
        s in table
        for s in ("┌", "┐", "├", "┤", "└", "┘", "│", "Clause", "Failed")
    )


def test_the_table_has_a_heading(capsys: pytest.CaptureFixture[str]) -> None:
    assert "Per-clause breakdown:" in _printed_table({"5": 0}, capsys)


def test_each_row_holds_the_clause_and_its_failures(
    capsys: pytest.CaptureFixture[str],
) -> None:
    table = _printed_table({"5": 1, "6": 0}, capsys)
    assert [_cells(table, "5"), _cells(table, "6")] == [["5", "1"], ["6", "0"]]


def test_the_table_has_no_percentage_column(
    capsys: pytest.CaptureFixture[str],
) -> None:
    table = _printed_table({"5": 1}, capsys)
    assert not any(s in table for s in ("Percentage", "%"))


def test_the_rows_run_in_natural_order(capsys: pytest.CaptureFixture[str]) -> None:
    table = _printed_table({"25": 0, "5": 0}, capsys)
    assert table.index("│ 5") < table.index("│ 25")


def test_a_clause_with_failures_takes_the_red_code(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with patch.object(run_tests_common, "RED", "<red>"):
        run_tests_common.print_clause_breakdown({"5": 1})
    assert "│<red> 5 " in capsys.readouterr().out


def test_a_clause_without_failures_takes_the_green_code(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with patch.object(run_tests_common, "GREEN", "<green>"):
        run_tests_common.print_clause_breakdown({"5": 0})
    assert "│<green> 5 " in capsys.readouterr().out


def test_a_row_without_a_color_code_is_left_plain(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with patch.object(run_tests_common, "GREEN", ""):
        run_tests_common.print_clause_breakdown({"5": 0})
    assert "│ 5      │      0 │" in capsys.readouterr().out
