"""Tests for the walk that finds the files a length cap does not admit.

Each tree below puts a file of exactly the cap's length beside one a single
line longer, because the cap is a boundary and a comparison written the wrong
way round agrees with a right one everywhere except across it. The suffixes and
the directory both vary too: a walk that read every file, or only the top of
the tree, would answer the same as this one on a tree where neither happened.
"""

from pathlib import Path

from lib.python.source_line_limit import line_count, over_limit, sources_under

SUFFIXES = (".cpp", ".h")


def written(path: Path, lines: int) -> Path:
    """Write a file of *lines* newline-terminated lines at *path*."""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("x\n" * lines, encoding="utf-8")
    return path


def tree(root: Path) -> Path:
    """Build a tree holding a file at the cap, one over it, and one ignored."""
    written(root / "at_the_cap.cpp", 3)
    written(root / "nested" / "over_the_cap.h", 4)
    written(root / "notes.md", 9)
    return root


def test_a_file_is_as_long_as_the_newlines_it_ends_its_lines_with(
    tmp_path: Path,
) -> None:
    """The count a breach is reported against is the count the gate made."""
    assert line_count(written(tmp_path / "counted.cpp", 7)) == 7


def test_a_file_whose_last_line_is_unterminated_is_not_counted_twice(
    tmp_path: Path,
) -> None:
    """A trailing fragment is not a line, which is what the shell also says."""
    path = tmp_path / "unterminated.cpp"
    path.write_text("x\nx\nx", encoding="utf-8")
    assert line_count(path) == 2


def test_the_walk_reaches_a_file_below_the_top_of_the_tree(
    tmp_path: Path,
) -> None:
    """A cap holds of the whole tree, so the walk cannot stop at its top."""
    names = [found.name for found in sources_under(tree(tmp_path), SUFFIXES)]
    assert names == ["at_the_cap.cpp", "over_the_cap.h"]


def test_the_walk_leaves_out_a_file_the_cap_does_not_cover(
    tmp_path: Path,
) -> None:
    """A document is not a source file however long it grows."""
    found = sources_under(tree(tmp_path), (".md",))
    assert [path.name for path in found] == ["notes.md"]


def test_a_file_of_exactly_the_cap_is_admitted(tmp_path: Path) -> None:
    """The cap is a length a file may reach rather than one it may not."""
    written(tmp_path / "at_the_cap.cpp", 3)
    assert not over_limit((tmp_path,), 3, SUFFIXES)


def test_a_file_one_line_over_the_cap_is_named_with_its_length(
    tmp_path: Path,
) -> None:
    """A breach is reported as the file and the number that broke it."""
    over = written(tmp_path / "over_the_cap.cpp", 4)
    assert over_limit((tmp_path,), 3, SUFFIXES) == [(over, 4)]


def test_every_root_the_gate_scans_is_walked(tmp_path: Path) -> None:
    """A gate naming two directories is not mirrored by a walk of one."""
    written(tmp_path / "first" / "short.cpp", 1)
    over = written(tmp_path / "second" / "long.cpp", 4)
    roots = (tmp_path / "first", tmp_path / "second")
    assert over_limit(roots, 3, SUFFIXES) == [(over, 4)]
