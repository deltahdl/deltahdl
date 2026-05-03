"""Shared helpers for test_main.py and test_main_run.py."""

from pathlib import Path
from types import SimpleNamespace
from typing import Any


def make_input_file(tmp_path: Path) -> Path:
    """Create a minimal test input file and return its path."""
    f = tmp_path / "test_input.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
        encoding="utf-8",
    )
    return f


def parser_response() -> dict[str, Any]:
    """Return a standard single-test clause response."""
    return {"clause": "6.1", "rationale": "r",
            "suite_name": "Parsing", "test_name": "T"}


def run_args(tmp_path: Path, **overrides: Any) -> SimpleNamespace:
    """Build a SimpleNamespace with all required _run args."""
    defaults: dict[str, Any] = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path), "dry_run": False,
        "lrm": str(tmp_path / "lrm.txt"), "max_lines": 1000,
        "suite": "S", "test": "T", "issue": None, "organization": None,
        "repo": None, "no_commit": False, "continue_session": False,
        "against": "",
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)
