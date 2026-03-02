"""Unit tests for convert_table argument parsing."""

import pytest

import convert_table


def test_valid_numeric_clause(tmp_path):
    """parse_args accepts a valid numeric clause."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_table.parse_args(["--lrm", str(lrm), "--clause", "4"])
    assert args.clause == "4"


def test_valid_dotted_clause(tmp_path):
    """parse_args accepts a dotted clause like '6.3.1'."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_table.parse_args(
        ["--lrm", str(lrm), "--clause", "6.3.1"],
    )
    assert args.clause == "6.3.1"


def test_valid_annex_clause(tmp_path):
    """parse_args accepts an uppercase-letter clause like 'A.1.2'."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_table.parse_args(
        ["--lrm", str(lrm), "--clause", "A.1.2"],
    )
    assert args.clause == "A.1.2"


def test_valid_max_depth_clause(tmp_path):
    """parse_args accepts a clause at maximum depth V.W.X.Y.Z."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_table.parse_args(
        ["--lrm", str(lrm), "--clause", "1.2.3.4.5"],
    )
    assert args.clause == "1.2.3.4.5"


def test_invalid_clause_exits(tmp_path):
    """parse_args exits for an invalid clause like '0.1'."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    with pytest.raises(SystemExit):
        convert_table.parse_args(
            ["--lrm", str(lrm), "--clause", "0.1"],
        )


def test_too_deep_clause_exits(tmp_path):
    """parse_args exits for a clause deeper than V.W.X.Y.Z."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    with pytest.raises(SystemExit):
        convert_table.parse_args(
            ["--lrm", str(lrm), "--clause", "1.2.3.4.5.6"],
        )


def test_missing_lrm_exits():
    """parse_args exits when --lrm file does not exist."""
    with pytest.raises(SystemExit):
        convert_table.parse_args(
            ["--lrm", "/no/such/file.pdf", "--clause", "4"],
        )


def test_lrm_is_path_object(tmp_path):
    """parse_args returns lrm as a Path object."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_table.parse_args(["--lrm", str(lrm), "--clause", "4"])
    assert args.lrm == lrm
