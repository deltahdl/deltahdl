"""Shared subprocess stubs for pytest-based test suites."""

from unittest.mock import MagicMock


def make_stub_completed(
    stdout: str = "", returncode: int = 0, stderr: str = "",
) -> MagicMock:
    """Return a stubbed ``CompletedProcess``-shaped MagicMock."""
    completed = MagicMock()
    completed.returncode = returncode
    completed.stdout = stdout
    completed.stderr = stderr
    return completed
