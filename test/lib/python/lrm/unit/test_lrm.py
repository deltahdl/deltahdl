"""Tests for lib.lrm."""

from lib.python.lrm import build_lrm_read_instruction


def test_lrm_read_general_subclause() -> None:
    """General subclause (X.1) does not add 'Also read General'."""
    result = build_lrm_read_instruction("6.1", "/lrm.pdf")
    assert "Also read" not in result


def test_lrm_read_non_general_adds_context() -> None:
    """Non-general subclause adds 'Also read General or Overview'."""
    result = build_lrm_read_instruction("6.3", "/lrm.pdf")
    assert "General or Overview" in result


def test_lrm_read_deep_includes_ancestors() -> None:
    """Deep subclause includes ancestor list."""
    result = build_lrm_read_instruction("6.3.2", "/lrm.pdf")
    assert "§6.3" in result


def test_lrm_read_includes_lrm_path() -> None:
    """Instruction includes the LRM path."""
    result = build_lrm_read_instruction("4.1", "/my/lrm.pdf")
    assert "/my/lrm.pdf" in result


def test_lrm_read_includes_subclause() -> None:
    """Instruction includes the subclause number."""
    result = build_lrm_read_instruction("9.2.1", "/lrm.pdf")
    assert "§9.2.1" in result
