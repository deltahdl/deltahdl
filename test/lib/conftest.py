"""Shared fixtures for lib test suite."""

import sys
from pathlib import Path

# Add repo root to sys.path so we can import the lib package.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
