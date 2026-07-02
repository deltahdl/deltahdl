"""Unit tests for satisfy_subclause.mutators.clang_format_changed.

Covers extension filtering (only .cpp/.h are formatted) and the exact
clang-format invocation used before a mutator commit lands.
"""

from typing import Any
from unittest.mock import patch

from satisfy_subclause.mutators import clang_format_changed


def _patched_run() -> Any:
    """Patch the subprocess.run shim used to invoke clang-format."""
    return patch("satisfy_subclause.mutators.subprocess.run")


def test_clang_format_changed_invokes_google_style_on_cpp_and_h() -> None:
    """.cpp and .h files are passed to clang-format -i --style=google."""
    with _patched_run() as mock_run:
        clang_format_changed(["a.cpp", "b.h"])
    assert mock_run.call_args[0][0] == [
        "clang-format", "-i", "--style=google", "a.cpp", "b.h",
    ]


def test_clang_format_changed_filters_out_non_cpp() -> None:
    """Python and CMake paths are dropped from the clang-format argv."""
    with _patched_run() as mock_run:
        clang_format_changed(["a.cpp", "x.py", "CMakeLists.txt"])
    assert mock_run.call_args[0][0] == [
        "clang-format", "-i", "--style=google", "a.cpp",
    ]


def test_clang_format_changed_no_cpp_is_a_noop() -> None:
    """With no C++ paths, clang-format is never invoked."""
    with _patched_run() as mock_run:
        clang_format_changed(["x.py", "CMakeLists.txt"])
    assert mock_run.called is False
