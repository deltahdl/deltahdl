"""Unit tests for convert_figure.__main__ module."""

import runpy
from unittest.mock import patch


def test_main_module_calls_main():
    """__main__.py calls convert_figure.main()."""
    with patch("convert_figure.main") as mock_main:
        runpy.run_module(
            "convert_figure", run_name="__main__", alter_sys=False,
        )
    assert mock_main.called
