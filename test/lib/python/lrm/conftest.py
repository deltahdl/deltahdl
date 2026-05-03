"""Shared fixtures for lib.lrm tests."""

from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

import pytest
from pypdf import PdfWriter


@pytest.fixture()
def nested_outline() -> list[tuple[int, str, int]]:
    """A 4-level outline used across lrm tests."""
    return [
        (1, "23 Tasks and functions", 100),
        (2, "23.1 Introduction", 100),
        (2, "23.2 Tasks", 110),
        (3, "23.2.1 Task declarations", 110),
        (3, "23.2.2 Task return", 112),
        (1, "24 Classes", 130),
    ]


@pytest.fixture()
def blank_pdf(tmp_path: Path) -> str:
    """Write a single-page PDF with no outline; return its path."""
    path = tmp_path / "blank.pdf"
    writer = PdfWriter()
    writer.add_blank_page(width=72, height=72)
    with open(path, "wb") as fp:
        writer.write(fp)
    return str(path)


@pytest.fixture()
def make_pdf(
    tmp_path: Path,
) -> Callable[[str, int, Sequence[tuple[int, str, int]]], str]:
    """Return a builder that writes a PDF with a bookmark outline.

    Outline entries are ``(depth, title, page_1indexed)``. Depth 1 is
    a top-level bookmark; depth 2 is its child; etc.
    """
    def _make(
        name: str,
        num_pages: int,
        outline: Sequence[tuple[int, str, int]],
    ) -> str:
        path = tmp_path / name
        writer = PdfWriter()
        for _ in range(num_pages):
            writer.add_blank_page(width=72, height=72)
        stack: list[tuple[int, Any]] = []
        for depth, title, page in outline:
            while stack and stack[-1][0] >= depth:
                stack.pop()
            parent = stack[-1][1] if stack else None
            handle = writer.add_outline_item(title, page - 1, parent=parent)
            stack.append((depth, handle))
        with open(path, "wb") as fp:
            writer.write(fp)
        return str(path)
    return _make
