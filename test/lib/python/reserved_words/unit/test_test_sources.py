"""No test in this repository declares a name Table B.1 has already taken.

The subject is the test tree as it stands. A source added later inherits the
requirement without anything here naming it, which is the point: what this
guards against is an author reaching for an ordinary English word that the
standard happens to reserve, and a test that then passes on an input which
never parsed.
"""

from pathlib import Path

from lib.python import reserved_words

REPO_ROOT = Path(__file__).resolve().parents[5]

# Every tree that holds SystemVerilog written into C++ string literals: the
# tests themselves and the scaffolding they share.
SOURCE_DIRS = ("test/src", "lib/cpp")


def sources() -> list[Path]:
    """Every C++ source and header the test tiers are written in."""
    found: list[Path] = []
    for directory in SOURCE_DIRS:
        for suffix in ("*.cpp", "*.h"):
            found.extend((REPO_ROOT / directory).rglob(suffix))
    return sorted(found)


def taken_names() -> dict[str, list[str]]:
    """Map each source to the reserved names it declares, where it does."""
    found: dict[str, list[str]] = {}
    for path in sources():
        named = reserved_words.reserved_declarations(
            path.read_text(encoding="utf-8")
        )
        if named:
            found[str(path.relative_to(REPO_ROOT))] = named
    return found


def test_the_test_tiers_are_written_in_sources_this_reading_can_find() -> None:
    """An empty tree would make the assertion below hold for the wrong reason."""
    assert sources()


def test_no_test_declares_a_name_the_standard_has_reserved() -> None:
    """A declaration naming a keyword is not a declaration."""
    assert not taken_names()
