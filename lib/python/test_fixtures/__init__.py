"""Shared test fixtures."""

import io
import sys
from types import ModuleType, SimpleNamespace
from typing import Any, Callable, cast

import pytest


def argv_without_flag(base: list[str], flag: str) -> list[str]:
    """Return *base* with *flag* and its value removed."""
    return [v for i, v in enumerate(base)
            if flag not in (base[max(0, i - 1)], v)]


def main_enables_line_buffering(
    monkeypatch: pytest.MonkeyPatch,
    module: ModuleType,
    make_args_fn: Callable[..., Any],
) -> bool:
    """Return whether *module*.main() reconfigures stdout for line buffering."""
    configured: list[dict[str, Any]] = []
    original = cast(io.TextIOWrapper, sys.stdout).reconfigure

    def mock_reconfigure(**kwargs: Any) -> None:
        configured.append(kwargs)
        return original(**kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(module, "_run", lambda _: None)
    monkeypatch.setattr(module, "_parse_args", make_args_fn)
    module.main()
    return any(k.get("line_buffering") for k in configured)


def capture_help_output(
    parse_func: Callable[[], Any],
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> str:
    """Call *parse_func* with ``--help`` and return captured stdout."""
    monkeypatch.setattr(sys, "argv", ["prog", "--help"])
    try:
        parse_func()
    except SystemExit:
        pass
    return capsys.readouterr().out


CLASSIFY_BASE_ARGV = [
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
    "--organization", "testorg",
    "--repo", "testrepo",
    "--max-lines", "1000",
]


def make_classify_args(**overrides: Any) -> SimpleNamespace:
    """Build a SimpleNamespace with classify-script base args."""
    defaults: dict[str, Any] = {
        "file": "/path/to/test.cpp",
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)
