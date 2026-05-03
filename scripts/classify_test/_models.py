"""Data classes for classify_test parsing and classification."""

from dataclasses import dataclass, field


@dataclass
class Classification:
    """Classification metadata produced by Claude for a test block.

    Bundling these into a single sub-record keeps :class:`TestBlock`
    under the seven-instance-attribute cap that pylint enforces, while
    still letting mypy see every field as a declared name.
    """

    prefix: str | None = None
    clause: str | None = None
    rationale: str | None = None
    prefix_rationale: str | None = None
    original_suite_name: str | None = None
    original_test_name: str | None = None


@dataclass
class TestBlock:
    """A single TEST/TEST_F/TEST_P block with classification metadata."""

    suite_name: str
    test_name: str
    lines: list[str]
    preceding_comments: list[str]
    classification: Classification = field(default_factory=Classification)


@dataclass
class PreambleItem:
    """A preamble declaration (struct, enum, helper function, etc.)."""

    lines: list[str]


@dataclass
class ParsedFile:
    """Result of parsing a standalone test file."""

    includes: list[str]
    using_line: str | None
    has_namespace_wrapper: bool
    global_preamble: list[PreambleItem]
    section_preamble: list[PreambleItem]
    all_tests: list[TestBlock]
    source_filename: str | None = None
