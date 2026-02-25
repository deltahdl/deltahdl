"""Unit tests for argument parsing and orchestration in convert_figure."""

from unittest.mock import MagicMock

import pytest

import convert_figure
from convert_figure import Figure, Node

_run = getattr(convert_figure, "_run")


# ---- parse_args ------------------------------------------------------------


def test_parse_args_valid_clause(tmp_path):
    """parse_args accepts a valid numeric clause."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_figure.parse_args(["--lrm", str(lrm), "--clause", "4"])
    assert args.clause == "4"


def test_parse_args_valid_dotted_clause(tmp_path):
    """parse_args accepts a dotted clause like '6.3.1'."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_figure.parse_args(
        ["--lrm", str(lrm), "--clause", "6.3.1"],
    )
    assert args.clause == "6.3.1"


def test_parse_args_valid_annex_clause(tmp_path):
    """parse_args accepts an uppercase-letter clause like 'A.1.2'."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_figure.parse_args(
        ["--lrm", str(lrm), "--clause", "A.1.2"],
    )
    assert args.clause == "A.1.2"


def test_parse_args_invalid_clause_exits(tmp_path):
    """parse_args exits for an invalid clause like '0.1'."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    with pytest.raises(SystemExit):
        convert_figure.parse_args(
            ["--lrm", str(lrm), "--clause", "0.1"],
        )


def test_parse_args_too_deep_clause_exits(tmp_path):
    """parse_args exits for a clause deeper than V.W.X.Y.Z."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    with pytest.raises(SystemExit):
        convert_figure.parse_args(
            ["--lrm", str(lrm), "--clause", "1.2.3.4.5.6"],
        )


def test_parse_args_missing_lrm_exits():
    """parse_args exits when --lrm file does not exist."""
    with pytest.raises(SystemExit):
        convert_figure.parse_args(
            ["--lrm", "/no/such/file.pdf", "--clause", "4"],
        )


def test_parse_args_lrm_path(tmp_path):
    """parse_args stores the LRM path."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    args = convert_figure.parse_args(["--lrm", str(lrm), "--clause", "4"])
    assert args.lrm == lrm


# ---- main ------------------------------------------------------------------


def test_main_calls_run(tmp_path, monkeypatch):
    """main delegates to _run after parsing args."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    called = {}

    def fake_run(lrm_path, clause):
        called["lrm"] = lrm_path
        called["clause"] = clause

    monkeypatch.setattr(convert_figure, "_run", fake_run)
    convert_figure.main(["--lrm", str(lrm), "--clause", "4.4"])
    assert called["clause"] == "4.4"


# ---- _run ------------------------------------------------------------------


def test_run_prints_dot_to_stdout(tmp_path, monkeypatch, capsys):
    """_run prints DOT output to stdout."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    fig = Figure(
        number="4-1",
        title="T",
        graph_name="Figure_4_1",
        nodes=(Node(node_id="A", label="A"),),
        edges=(),
    )
    mock_doc = MagicMock()
    mock_doc.__len__ = lambda self: 1
    mock_page = MagicMock()
    monkeypatch.setattr(convert_figure, "open_document", lambda p: mock_doc)
    monkeypatch.setattr(
        convert_figure, "find_clause_pages", lambda d, c: [0],
    )
    monkeypatch.setattr(
        convert_figure, "find_figure_captions",
        lambda d, p, c: [(0, "4-1", "T", 690.0)],
    )
    monkeypatch.setattr(
        convert_figure, "extract_figure",
        lambda page, figure_number, figure_title, caption_y: fig,
    )

    def getitem(_self, _idx):
        return mock_page

    type(mock_doc).__getitem__ = getitem
    _run(lrm, "4")
    assert "digraph" in capsys.readouterr().out


def _setup_run(tmp_path, monkeypatch):
    """Create a dummy LRM and patch open_document."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    mock_doc = MagicMock()
    mock_doc.__len__ = lambda _self: 1
    monkeypatch.setattr(convert_figure, "open_document", lambda p: mock_doc)
    return lrm, mock_doc


def test_run_no_figures_exits(tmp_path, monkeypatch):
    """_run exits with error when no figures are found."""
    lrm, _ = _setup_run(tmp_path, monkeypatch)
    monkeypatch.setattr(
        convert_figure, "find_clause_pages", lambda d, c: [0],
    )
    monkeypatch.setattr(
        convert_figure, "find_figure_captions", lambda d, p, c: [],
    )
    with pytest.raises(SystemExit):
        _run(lrm, "99")


def test_run_no_pages_exits(tmp_path, monkeypatch):
    """_run exits with error when no clause pages are found."""
    lrm, _ = _setup_run(tmp_path, monkeypatch)
    monkeypatch.setattr(
        convert_figure, "find_clause_pages", lambda d, c: [],
    )
    with pytest.raises(SystemExit):
        _run(lrm, "99")
