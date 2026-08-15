"""Whether every subclause a C++ source cites names a real clause.

A report deltahdl makes carries the subclause of IEEE 1800-2023 whose rule it
enforces, written as ``Subclause("6.20.3")`` at the emission site. A reader who
follows one of those citations to check the tool is right has to find something
at that number. This module answers whether they will, by comparing the
citations a tree contains against the identifiers the standard defines.

It compares two sets of strings and reads no clause. Whether a citation is the
*right* clause for the rule it reports is a reading of the standard, and that is
a reviewer's job rather than a gate's.

The identifiers live in ``clauses.txt`` beside this file, committed because
``~/LRM.pdf`` is a local file no CI runner has. That file's own header says how
it was derived and how to regenerate it.

This is a script rather than a module under ``lib/python/`` because nothing but
the check itself would call it. ``assert-no-test-only-python-definition`` in
``.github/workflows/scripts.yml`` reports a ``lib/python/`` definition whose only
uses are in its own tests, and every function here would be one.
"""

import re
from pathlib import Path

CLAUSES_FILE = Path(__file__).parent / "clauses.txt"

_CITATION_RE = re.compile(r'Subclause\("([^"]*)"\)')


def strip_cpp_comments(text: str) -> str:
    """Return `text` with every C++ comment replaced by a space.

    Citations are read out of code and not out of prose about code. The
    docstring on DiagEngine in src/common/diagnostic.h names
    ``Subclause("§11.4.14")`` to say what not to write, and a scan that read
    comments would take that counterexample for a citation and report the file
    it is teaching against.

    A comment is replaced rather than deleted so that nothing on either side of
    it is joined into a token that was never written.
    """
    out: list[str] = []
    i = 0
    end = len(text)
    while i < end:
        pair = text[i:i + 2]
        if pair == "//":
            newline = text.find("\n", i)
            i = end if newline == -1 else newline
            out.append(" ")
        elif pair == "/*":
            close = text.find("*/", i + 2)
            i = end if close == -1 else close + 2
            out.append(" ")
        elif text[i] == '"':
            j = i + 1
            while j < end and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append(text[i:min(j + 1, end)])
            i = min(j + 1, end)
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def cited_subclauses(text: str) -> set[str]:
    """Every subclause `text` cites, ignoring the ones its comments name."""
    return set(_CITATION_RE.findall(strip_cpp_comments(text)))


def known_subclauses(clauses_file: Path = CLAUSES_FILE) -> set[str]:
    """Every clause identifier IEEE 1800-2023 defines.

    Lines opening with ``#`` are the file's header and name no clause.
    """
    lines = clauses_file.read_text(encoding="utf-8").splitlines()
    return {line.strip() for line in lines
            if line.strip() and not line.startswith("#")}


def citations_in_tree(root: Path) -> dict[str, set[str]]:
    """Every subclause each ``.cpp`` or ``.h`` under `root` cites, by path.

    A file citing nothing is left out, so a caller reporting what it found
    names only files that have something to say.

    The encoding is named rather than left to the locale, because a source
    under src/ carries a section sign in its comments and a runner whose
    locale is not UTF-8 would fail to decode it.
    """
    found: dict[str, set[str]] = {}
    for path in sorted(root.rglob("*")):
        if path.suffix not in (".cpp", ".h"):
            continue
        cited = cited_subclauses(path.read_text(encoding="utf-8"))
        if cited:
            found[str(path)] = cited
    return found


def invalid_citations(
    root: Path, clauses_file: Path = CLAUSES_FILE
) -> dict[str, set[str]]:
    """Every citation under `root` that names no clause of the standard.

    Keyed by path so a failure says which file to open. Empty when every
    citation names something, which is the state this is a gate on.
    """
    known = known_subclauses(clauses_file)
    bad: dict[str, set[str]] = {}
    for path, cited in citations_in_tree(root).items():
        unknown = cited - known
        if unknown:
            bad[path] = unknown
    return bad


def main(root: Path = Path("src")) -> int:
    """Report every citation under `root` naming no clause; 1 if any does.

    Each report is a GitHub Actions error annotation, so a failure points at
    the file rather than only saying a count.
    """
    bad = invalid_citations(root)
    for path in sorted(bad):
        for cited in sorted(bad[path]):
            print(
                f"::error file={path}::{path} cites {cited}, which is not a"
                " clause of IEEE 1800-2023; cite the clause stating the rule"
            )
    return 1 if bad else 0
