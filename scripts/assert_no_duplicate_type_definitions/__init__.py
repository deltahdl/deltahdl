"""Report a class, struct, union or enum defined by two headers at one scope.

A type defined twice compiles for as long as no translation unit sees both
headers, and fails everywhere the moment one does. `enum class
AssertionSeverity : uint8_t` stood in both src/simulator/dpi_runtime.h and
src/simulator/sva_engine_sequences.h with the same four enumerators until
473260321 made src/simulator/sim_context.h include a header that reaches the
second, and every clang-tidy-test-shard-* job of run 33185965619 then failed
with "redefinition of 'AssertionSeverity'". The commit that broke the build
added no definition at all -- it added one #include -- so the twenty red shards
named a change about assertion sampling and nothing connected them to the two
headers.

jscpd does not cover it. copy-paste-src measures duplicated token runs against
a minimum size, and a duplicated enumeration is about six lines, which is under
that minimum by the nature of the thing being duplicated.
"""

import re
from collections.abc import Iterable, Iterator
from pathlib import Path

# The trees a header is read from. lib/cpp holds the test helpers and test/src
# the cases themselves, and a type defined in both a header under src/ and one
# under test/ breaks a translation unit exactly as two under src/ do.
ROOTS = (Path("src"), Path("lib"), Path("test"))

# `namespace delta {` and `namespace delta::detail {`. The components are kept
# so that two types of one name under different namespaces are told apart,
# which they are: they are two types.
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w:]*)\s*\{")

# `namespace {`. §7.3.1.1 of the C++ standard gives an unnamed namespace
# internal linkage, so two headers can each hold one without colliding -- but
# a header with an unnamed namespace is its own defect and not this one's, so
# the frame is named rather than skipped, and named the same in every file so
# that two such definitions still read as one scope.
ANONYMOUS_NAMESPACE_RE = re.compile(r"^\s*namespace\s*\{")

# The head of a definition: an optional single-line template prefix, one of the
# four keywords, and the name. `enum class` and `enum struct` are written out
# ahead of the bare `enum` so the alternation does not stop at the keyword and
# read `class` as the name.
TYPE_HEAD_RE = re.compile(
    r"^\s*(?:template\s*<[^>]*>\s*)?"
    r"(?:class|struct|union|enum\s+class|enum\s+struct|enum)\s+"
    r"(?:__attribute__\s*\(\([^)]*\)\)\s*)?"
    r"([A-Za-z_]\w*)"
)

HEADER_SUFFIX = ".h"


# Everything that looks like code but is not: a line comment, a block comment
# terminated or running to the end of the file, a string literal terminated or
# running to the end of the file, and a character literal of one character.
#
# The unterminated alternatives follow their terminated ones so that a
# well-formed comment or literal is taken whole; the regex engine tries them in
# the order written and the terminated one wins wherever it matches.
#
# A character literal is held to exactly one character so that the digit
# separators of `1'000'000` are not read as one. A `{` written as '{' is why
# character literals are read at all.
_COMMENT_OR_LITERAL = re.compile(
    r"//[^\n]*"
    r"|/\*.*?\*/"
    r"|/\*.*"
    r'|"(?:\\.|[^"\\])*"'
    r'|"(?:\\.|[^"\\])*'
    r"|'(?:\\.|[^'\\\n])'",
    re.DOTALL,
)


def _blank(match: "re.Match[str]") -> str:
    """Return `match` as spaces, keeping every newline it spans."""
    return "".join("\n" if char == "\n" else " " for char in match.group(0))


def strip_comments_and_strings(text: str) -> str:
    """Return `text` with every comment and literal blanked, line for line.

    A comment holding the word `class` or a brace would otherwise be read as
    code, and a brace inside a string literal would throw the depth count off
    for the rest of the file, which puts every later definition at the wrong
    scope.

    Every newline is kept and every other removed character becomes a space.
    The line a definition stands on is what this module reports, so a stripper
    that collapsed a block comment would move every definition after it; and a
    space rather than nothing keeps the tokens on either side of a comment from
    being joined into one that was never written.
    """
    return _COMMENT_OR_LITERAL.sub(_blank, text)


def _opens_a_body(lines: list[str], start: int) -> bool:
    """Whether the statement beginning at `lines[start]` opens a braced body.

    `class Frame;` declares and `class Frame {` defines, and the two are told
    apart by which of `{` and `;` comes first. The scan runs on past the head
    line because a base-clause may put the brace on the next one, and stops at
    the first of the two characters wherever it stands.

    A statement that reaches the end of the file without either is not a
    definition, which is what an unterminated header would leave.
    """
    for line in lines[start:]:
        for char in line:
            if char == "{":
                return True
            if char == ";":
                return False
    return False


def _is_specialization(line: str, after_name: int) -> bool:
    """Whether the name at `after_name` is followed by a template argument list.

    `template <> struct Traits<int> {` defines no new name: it specializes the
    primary template, which some other header declares. Reading it as a
    definition of `Traits` would report the primary and the specialization as
    two definitions of one name.
    """
    rest = line[after_name:].lstrip()
    return rest.startswith("<")


def definitions(text: str) -> list[tuple[str, str, int]]:
    """Return every type defined at namespace scope in `text`.

    Each entry is the namespace path the definition stands in, the name it
    defines, and the 1-based line its head is written on. The path is joined
    with `::` and is empty at file scope.

    Only namespace scope is read. A type nested in a class is named by that
    class as well, so it cannot collide with one of the same name nested in
    another; and a type declared inside a function body is not visible to
    another translation unit at all.
    """
    lines = strip_comments_and_strings(text).splitlines()
    found: list[tuple[str, str, int]] = []
    frames: list[list[str]] = []
    depth = 0
    for index, line in enumerate(lines):
        namespace = NAMESPACE_RE.match(line)
        anonymous = ANONYMOUS_NAMESPACE_RE.match(line)
        # A frame is one brace, so namespace scope is where every open brace is
        # a namespace's. A class body or a function body puts the depth ahead
        # of the frames and keeps it there until it closes.
        if namespace is None and anonymous is None and depth == len(frames):
            head = TYPE_HEAD_RE.match(line)
            if (
                head is not None
                and not _is_specialization(line, head.end(1))
                and _opens_a_body(lines, index)
            ):
                path = "::".join(part for frame in frames for part in frame)
                found.append((path, head.group(1), index + 1))
        if namespace is not None:
            frames.append(namespace.group(1).split("::"))
        elif anonymous is not None:
            frames.append(["(anonymous)"])
        depth += line.count("{") - line.count("}")
        del frames[depth:]
    return found


def headers(roots: Iterable[Path]) -> Iterator[Path]:
    """Yield every header under `roots`, in a settled order.

    Only headers are read. A definition in a .cpp file is visible to that file
    alone, so two of them are not the collision this reports; and a header is
    what an #include reaches.
    """
    for root in roots:
        yield from sorted(root.rglob(f"*{HEADER_SUFFIX}"))


def duplicate_definitions(
    roots: Iterable[Path] = ROOTS,
) -> dict[tuple[str, str], list[tuple[Path, int]]]:
    """Return every scoped name defined by more than one header under `roots`.

    Keyed by the namespace path and the name together, so two types of one name
    in different namespaces are two types and not a duplicate.

    A name defined twice by one header is not a duplicate either: that is what
    a definition guarded by #if/#else looks like from here, and the compiler
    settles which of the two it takes. So the sites of a name are reduced to
    one per header before the count is read.
    """
    sites: dict[tuple[str, str], list[tuple[Path, int]]] = {}
    for path in headers(roots):
        seen: set[tuple[str, str]] = set()
        for namespace, name, line in definitions(path.read_text()):
            key = (namespace, name)
            if key in seen:
                continue
            seen.add(key)
            sites.setdefault(key, []).append((path, line))
    return {key: found for key, found in sites.items() if len(found) > 1}


def main(roots: Iterable[Path] = ROOTS) -> int:
    """Report every duplicate under `roots`; 1 if there is one.

    Each report is a GitHub Actions error annotation on one of the two headers,
    so the run points at a file rather than only naming a type. Both headers
    are annotated, because neither is the one to change without reading the
    other.
    """
    duplicates = duplicate_definitions(roots)
    for (namespace, name), sites in sorted(duplicates.items()):
        scoped = f"{namespace}::{name}" if namespace else name
        where = ", ".join(f"{path}:{line}" for path, line in sites)
        for path, line in sites:
            print(
                f"::error file={path},line={line}::{scoped} is defined by"
                f" {len(sites)} headers ({where}); a translation unit that"
                " includes two of them fails to compile, so one definition has"
                " to be the only one"
            )
    return 1 if duplicates else 0
