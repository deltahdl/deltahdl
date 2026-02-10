"""Fixtures specific to run_sim_tests tests."""

import pytest


@pytest.fixture()
def sim_test_tree(tmp_path):
    """Create a fake sim-tests directory with .sv/.expected pairs.

    Returns the tmp_path containing:
      hello.sv / hello.expected  (matching pair)
      fail.sv / fail.expected    (pair where expected differs from what stub gives)
      orphan.sv                  (no .expected — should be ignored)
    """
    (tmp_path / "hello.sv").write_text("module hello; endmodule\n")
    (tmp_path / "hello.expected").write_text("Hello, World!\n")

    (tmp_path / "fail.sv").write_text("module fail; endmodule\n")
    (tmp_path / "fail.expected").write_text("expected output\n")

    # orphan — no matching .expected
    (tmp_path / "orphan.sv").write_text("module orphan; endmodule\n")

    return tmp_path
