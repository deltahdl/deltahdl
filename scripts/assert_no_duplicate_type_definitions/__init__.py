import re
from collections.abc import Iterable, Iterator
from pathlib import Path

ROOTS = (Path("src"), Path("lib"), Path("test"))

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w:]*)\s*\{")

ANONYMOUS_NAMESPACE_RE = re.compile(r"^\s*namespace\s*\{")

TYPE_HEAD_RE = re.compile(
    r"^\s*(?:template\s*<[^>]*>\s*)?"
    r"(?:class|struct|union|enum\s+class|enum\s+struct|enum)\s+"
    r"(?:__attribute__\s*\(\([^)]*\)\)\s*)?"
    r"([A-Za-z_]\w*)"
)

HEADER_SUFFIX = ".h"


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
    return "".join("\n" if char == "\n" else " " for char in match.group(0))


def strip_comments_and_strings(text: str) -> str:
    return _COMMENT_OR_LITERAL.sub(_blank, text)


def _opens_a_body(lines: list[str], start: int) -> bool:
    for line in lines[start:]:
        for char in line:
            if char == "{":
                return True
            if char == ";":
                return False
    return False


def _is_specialization(line: str, after_name: int) -> bool:
    rest = line[after_name:].lstrip()
    return rest.startswith("<")


def definitions(text: str) -> list[tuple[str, str, int]]:
    lines = strip_comments_and_strings(text).splitlines()
    found: list[tuple[str, str, int]] = []
    frames: list[list[str]] = []
    depth = 0
    for index, line in enumerate(lines):
        namespace = NAMESPACE_RE.match(line)
        anonymous = ANONYMOUS_NAMESPACE_RE.match(line)
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
    for root in roots:
        yield from sorted(root.rglob(f"*{HEADER_SUFFIX}"))


def duplicate_definitions(
    roots: Iterable[Path] = ROOTS,
) -> dict[tuple[str, str], list[tuple[Path, int]]]:
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
