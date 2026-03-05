"""Shared fixtures for implement_subclause unit tests."""

import subprocess
from unittest.mock import patch

import pytest


@pytest.fixture()
def popen_ok():
    """Patch subprocess.run with a successful mock; yield mock_run."""
    with patch("implement_subclause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=0,
        )
        yield mock_run
