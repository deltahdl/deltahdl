"""Unit tests for implement_clause.__main__ entry point."""

import importlib
import sys
from unittest.mock import patch


@patch("implement_clause.main")
def test_main_module_calls_main(mock_main):
    """Importing __main__ invokes main()."""
    sys.modules.pop("implement_clause.__main__", None)
    importlib.import_module("implement_clause.__main__")
    assert mock_main.called
