import re
from pathlib import Path

CLAUSES_FILE = Path(__file__).parent / "clauses.txt"

_CITATION_RE = re.compile(r'Subclause\("([^"]*)"\)')
_CALL_RE = re.compile(r"\b(?:Error|Warning)\s*\(")
_STRING_RE = re.compile(r'"((?:[^"\\]|\\.)*)"')
_NESTING_RE = re.compile(r""""(?:[^"\\]|\\.)*"|'(?:\\.|[^'\\])'|[()]""")


def strip_cpp_comments(text: str) -> str:
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
    return set(_CITATION_RE.findall(strip_cpp_comments(text)))


def diagnostic_call_arguments(text: str) -> list[str]:
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
    cited: dict[str, set[str]] = {}
    for path in sorted(root.rglob("*")):
        if path.suffix not in (".cpp", ".h"):
            continue
        text = path.read_text(encoding="utf-8")
        for message, subclause in message_subclause_pairs(text):
            cited.setdefault(message, set()).add(subclause)
    return {msg: subs for msg, subs in cited.items() if len(subs) > 1}


def known_subclauses(clauses_file: Path = CLAUSES_FILE) -> set[str]:
    lines = clauses_file.read_text(encoding="utf-8").splitlines()
    return {line.strip() for line in lines
            if line.strip() and not line.startswith("#")}


def citations_in_tree(root: Path) -> dict[str, set[str]]:
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
    known = known_subclauses(clauses_file)
    bad: dict[str, set[str]] = {}
    for path, cited in citations_in_tree(root).items():
        unknown = cited - known
        if unknown:
            bad[path] = unknown
    return bad


def main(root: Path = Path("src")) -> int:
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
