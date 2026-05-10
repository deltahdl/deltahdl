"""Unit tests for lib.python.claude_cli_streaming.build_env."""

from unittest.mock import patch

from lib.python.claude_cli_streaming import build_env


def test_build_env_drops_claudecode() -> None:
    """build_env removes the CLAUDECODE variable when set."""
    with patch.dict("os.environ", {"CLAUDECODE": "1"}, clear=False):
        env = build_env()
    assert "CLAUDECODE" not in env


def test_build_env_when_claudecode_unset() -> None:
    """build_env succeeds when CLAUDECODE is not set."""
    with patch.dict("os.environ", {}, clear=True):
        env = build_env()
    assert "CLAUDECODE" not in env


def test_build_env_preserves_other_vars() -> None:
    """build_env preserves unrelated environment variables."""
    with patch.dict("os.environ", {"BUILD_ENV_VAR": "value"}, clear=False):
        env = build_env()
    assert env.get("BUILD_ENV_VAR") == "value"
