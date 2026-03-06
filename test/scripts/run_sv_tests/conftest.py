"""Fixtures specific to run_sv_tests tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def rst(module_loader):
    """Load the run_sv_tests module."""
    return module_loader(
        "run_sv_tests",
        SCRIPTS_DIR / "run_sv_tests" / "__init__.py",
    )


@pytest.fixture()
def sv_test_tree(tmp_path):
    """Create a fake sv-tests directory tree with chapter dirs and .sv files.

    Returns the tmp_path containing:
      chapter-5/alpha.sv
      chapter-5/beta.sv
      chapter-6/gamma.sv
    """
    ch5 = tmp_path / "chapter-5"
    ch5.mkdir()
    (ch5 / "alpha.sv").write_text("module alpha; endmodule\n")
    (ch5 / "beta.sv").write_text("module beta; endmodule\n")

    ch6 = tmp_path / "chapter-6"
    ch6.mkdir()
    (ch6 / "gamma.sv").write_text("module gamma; endmodule\n")

    return tmp_path
