"""Two things a C++ source can get wrong about the subclauses it cites.

A report deltahdl makes carries the subclause of IEEE 1800-2023 whose rule it
enforces, written as ``Subclause("6.20.3")`` at the emission site. A reader who
follows one of those citations to check the tool is right has to find something
at that number, and two reports that read alike have to send them to the same
place. This module fails when either does not hold.

The first check compares the citations a tree contains against the identifiers
the standard defines, so a citation naming no clause at all is reported.

The second pairs each message with the subclause of the same call and reports a
message carried by more than one. Such a message sends a reader to a clause
chosen by which code path fired rather than by what they wrote, and it leaves a
test unable to say which rule it covers: ``ReportedError`` in
``lib/cpp/test_helpers/helpers_reported_error.h`` matches on message and
subclause, so a case naming the message alone is satisfied by either rule.

Neither check reads a clause. Whether a citation is the *right* clause for the
rule it reports is a reading of the standard and stays a reviewer's job; what
the second check answers is whether two sites agree with each other.

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
_CALL_RE = re.compile(r"\b(?:Error|Warning)\s*\(")
_STRING_RE = re.compile(r'"((?:[^"\\]|\\.)*)"')
# A string literal, a character literal, or a bare parenthesis. The two
# literals come first so that a parenthesis written inside one is read as part
# of it: src/parser/parser_verify.cpp reports "missing ')' in covergroup item",
# and that parenthesis closes nothing.
_NESTING_RE = re.compile(r""""(?:[^"\\]|\\.)*"|'(?:\\.|[^'\\])'|[()]""")


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


def diagnostic_call_arguments(text: str) -> list[str]:
    """The argument text of every ``Error`` and ``Warning`` call in `text`.

    A call is read as far as the parenthesis closing it, so an argument built
    by a nested call comes back with it -- which is what makes the
    ``std::format`` most messages are assembled by readable here.

    A call nothing closes is read to the end of `text`, which is what a source
    that does not compile would give.
    """
    found: list[str] = []
    for call in _CALL_RE.finditer(text):
        depth = 1
        end = len(text)
        for token in _NESTING_RE.finditer(text, call.end()):
            if token.group() == "(":
                depth += 1
            elif token.group() == ")":
                depth -= 1
                if depth == 0:
                    end = token.start()
                    break
        found.append(text[call.end():end])
    return found


def message_subclause_pairs(text: str) -> set[tuple[str, str]]:
    """Every diagnostic message in `text` beside the subclause its call names.

    The message is every string literal of the call outside its
    ``Subclause(…)``, joined. C++ joins adjacent literals, and a sentence too
    long for one line is written as several, so reading one literal would give
    a message no reader is ever shown -- which is how a stale assertion in
    ``test/src/unit/test_elaborator_annex_g_07.cpp`` hid from a search during
    #3058. A placeholder ``std::format`` fills in stays as it was written, so
    two reports differing only in the name they quote count as one message.

    A call naming two subclauses is left out, because it is one site choosing
    the clause its construct answers to rather than two sites disagreeing:
    ``src/parser/parser_items.cpp`` cites §13.3 for a task and §13.4 for a
    function from a single report, and ``src/elaborator/
    elaborator_port_binding.cpp`` cites §23.3.3.2 or §23.3.3.3 by the type the
    port was declared with. A call naming a subclause held in a variable is
    left out for the same reason, and by the same token: ``check_def`` in
    ``src/elaborator/elaborator_validate_config.cpp`` takes the subclause from
    its caller so that a collision involving a config reports §33.2.
    """
    pairs: set[tuple[str, str]] = set()
    for arguments in diagnostic_call_arguments(strip_cpp_comments(text)):
        cited = _CITATION_RE.findall(arguments)
        if len(cited) != 1:
            continue
        message = "".join(
            _STRING_RE.findall(_CITATION_RE.sub("", arguments))
        )
        if message:
            pairs.add((message, cited[0]))
    return pairs


def messages_citing_two_subclauses(root: Path) -> dict[str, set[str]]:
    """Every message under `root` reported under more than one subclause.

    Keyed by the message so a failure quotes the sentence a reader would see.
    Empty when every message names one rule, which is the state this is a gate
    on.
    """
    cited: dict[str, set[str]] = {}
    for path in sorted(root.rglob("*")):
        if path.suffix not in (".cpp", ".h"):
            continue
        text = path.read_text(encoding="utf-8")
        for message, subclause in message_subclause_pairs(text):
            cited.setdefault(message, set()).add(subclause)
    return {msg: subs for msg, subs in cited.items() if len(subs) > 1}


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
    """Report both faults under `root`; 1 if either is present.

    Each report is a GitHub Actions error annotation, so a failure points at
    the file rather than only saying a count. The two faults are reported in
    different words, because they are fixed differently and a reader should
    not have to work out which one fired.
    """
    bad = invalid_citations(root)
    for path in sorted(bad):
        for cited in sorted(bad[path]):
            print(
                f"::error file={path}::{path} cites {cited}, which is not a"
                " clause of IEEE 1800-2023; cite the clause stating the rule"
            )
    shared = messages_citing_two_subclauses(root)
    for message in sorted(shared):
        named = ", ".join(f"§{s}" for s in sorted(shared[message]))
        print(
            f'::error::"{message}" is reported under {named}; either one of'
            " those citations names the wrong clause, or the sites enforce two"
            " rules and the message has to tell them apart"
        )
    return 1 if bad or shared else 0
