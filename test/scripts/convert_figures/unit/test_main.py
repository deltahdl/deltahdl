"""Unit tests for convert_figures.__main__ module."""

import runpy
from unittest.mock import patch


def test_main_module_calls_main():
    """__main__.py calls convert_figures.main()."""
    with patch("convert_figures.main") as mock_main:
        runpy.run_module(
            "convert_figures", run_name="__main__", alter_sys=False,
        )
    assert mock_main.called
