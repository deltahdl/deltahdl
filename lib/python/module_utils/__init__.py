"""Utilities for dynamically loading Python modules in tests."""

import importlib.util
import sys
from pathlib import Path
from types import ModuleType


def load_module_from_path(module_name: str, path: Path) -> ModuleType:
    """Load a Python module from a file path."""
    spec = importlib.util.spec_from_file_location(module_name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module
