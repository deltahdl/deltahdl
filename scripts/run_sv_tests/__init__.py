import argparse
import ast
import glob
import json
import operator
import os
import re
import subprocess
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from functools import partial
from pathlib import Path
from typing import Any, Callable, NamedTuple
from xml.etree import ElementTree as ET

from lib.python.run_tests_common import (
    BINARY, GREEN, RED, REPO_ROOT, RESET, check_binary, print_result,
)

TEST_DIR = REPO_ROOT / "third_party" / "sv-tests" / "tests"


class Library(NamedTuple):
    files: tuple[str, ...]
    incdirs: tuple[str, ...]
    defines: tuple[str, ...]


_DEFINES_OF_LIBRARY_WITHOUT_FOREIGN_CODE: dict[str, tuple[str, ...]] = {
    "uvm": ("UVM_NO_DPI",),
    "uvm-1.2": ("UVM_NO_DPI",),
}


def load_libraries() -> dict[str, Library]:
    suite = TEST_DIR.parent
    entries = json.loads(
        (suite / "conf" / "runners" / "libs.json").read_text(encoding="utf-8"),
    )
    libraries: dict[str, Library] = {}
    for tag, entry in entries.items():
        files = [suite / "third_party" / p for p in entry["files"]]
        incdirs = [suite / "third_party" / p for p in entry["incdirs"]]
        for path in files + incdirs:
            if not path.exists():
                raise FileNotFoundError(
                    f"library '{tag}' names {path}, which is not checked out",
                )
        libraries[tag] = Library(
            tuple(str(p) for p in files),
            tuple(str(p) for p in incdirs),
            _DEFINES_OF_LIBRARY_WITHOUT_FOREIGN_CODE.get(tag, ()),
        )
    return libraries


def library_for(
    metadata: dict[str, str], libraries: dict[str, Library],
) -> Library:
    tags = metadata.get("tags", "").split()
    files: tuple[str, ...] = ()
    incdirs: tuple[str, ...] = ()
    defines: tuple[str, ...] = ()
    for tag, entry in libraries.items():
        if tag in tags:
            files += entry.files
            incdirs += entry.incdirs
            defines += entry.defines
    return Library(files, incdirs, defines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run CHIPS Alliance sv-tests against deltahdl."
    )
    parser.add_argument(
        "--junit-xml",
        metavar="FILE",
        help="Write JUnit XML results to FILE.",
    )
    parser.add_argument(
        "--chapter",
        metavar="N",
        help="Only run tests for the given chapter number (e.g. 5).",
    )
    return parser.parse_args()


def _natural_sort_key(text: str) -> list[Any]:
    return [int(tok) if tok.isdigit() else tok for tok in re.split(r"(\d+)", text)]


def collect_tests(chapter: str | None = None) -> list[str]:
    chapter_glob = f"chapter-{chapter}" if chapter else "chapter-*"
    pattern = str(TEST_DIR / chapter_glob / "**" / "*.sv")
    return sorted(glob.glob(pattern, recursive=True), key=_natural_sort_key)


def parse_metadata(path: str) -> dict[str, str]:
    text = Path(path).read_text(encoding="utf-8")
    match = re.search(r"/\*(.*?)\*/", text, re.DOTALL)
    if not match:
        return {}
    metadata: dict[str, str] = {}
    for line in match.group(1).splitlines():
        m = re.match(r"\s*:(\w+):\s*(.*)", line)
        if m:
            metadata[m.group(1)] = m.group(2).strip()
    return metadata


_UNARY_OPS: dict[type[ast.unaryop], Callable[[Any], Any]] = {
    ast.Not: operator.not_,
    ast.USub: operator.neg,
    ast.UAdd: operator.pos,
    ast.Invert: operator.invert,
}

_COMPARE_OPS: dict[type[ast.cmpop], Callable[[Any, Any], bool]] = {
    ast.Eq: operator.eq,
    ast.NotEq: operator.ne,
    ast.Lt: operator.lt,
    ast.LtE: operator.le,
    ast.Gt: operator.gt,
    ast.GtE: operator.ge,
    ast.In: lambda a, b: operator.contains(b, a),
    ast.NotIn: lambda a, b: not operator.contains(b, a),
}


def eval_node(node: ast.AST) -> Any:
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.Compare):
        left = eval_node(node.left)
        for op, comp in zip(node.ops, node.comparators):
            right = eval_node(comp)
            if not _COMPARE_OPS[type(op)](left, right):
                return False
            left = right
        return True
    if isinstance(node, ast.BoolOp):
        vals = [eval_node(v) for v in node.values]
        if isinstance(node.op, ast.And):
            return all(vals)
        return any(vals)
    if isinstance(node, ast.UnaryOp) and type(node.op) in _UNARY_OPS:
        return _UNARY_OPS[type(node.op)](eval_node(node.operand))
    raise ValueError(f"Unsupported node: {type(node).__name__}")


def try_string_equality(expr: str) -> bool | None:
    m = re.match(r"\(\s*'(.*)'\s*==\s*'(.*)'\s*\)$", expr)
    if m:
        return m.group(1) == m.group(2)
    return None


def check_assertions(stdout: str) -> tuple[bool, str]:
    for line in stdout.splitlines():
        match = re.search(r":assert:\s*(.*)", line)
        if not match:
            continue
        expr = match.group(1).strip()
        try:
            tree = ast.parse(expr, mode="eval")
            if not eval_node(tree.body):
                return False, f"Assertion failed: {expr}"
        except (SyntaxError, ValueError):
            result = try_string_equality(expr)
            if result is None:
                return False, f"Assertion parse error: {expr}"
            if not result:
                return False, f"Assertion failed: {expr}"
    return True, ""


_STAGE_OPTION_OF_MODE: dict[str, str | None] = {
    "simulation": None,
    "simulation_without_run": "--lint-only",
    "elaboration": "--lint-only",
    "parsing": "--parse-only",
    "preprocessing": "--parse-only",
}
_DEFAULT_TYPE = "parsing elaboration"


def run_mode(metadata: dict[str, str]) -> str:
    features = metadata.get("type", _DEFAULT_TYPE).split()
    for mode in _STAGE_OPTION_OF_MODE:
        if mode in features:
            return mode
    raise ValueError(f"no run mode among {features}")


def run_test(
    path: str,
    mode: str = "elaboration",
    defines: tuple[str, ...] | list[str] = (),
    library: Library = Library((), (), ()),
) -> tuple[bool, str, int]:
    option = _STAGE_OPTION_OF_MODE[mode]
    cmd = [str(BINARY)] if option is None else [str(BINARY), option]
    for d in (*library.defines, *defines):
        cmd.extend(["-D", d])
    for incdir in library.incdirs:
        cmd.append(f"+incdir+{incdir}")
    cmd.extend(library.files)
    cmd.append(path)
    result = subprocess.run(
        cmd,
        capture_output=True,
        timeout=30,
        check=False,
        text=True,
    )
    if mode != "simulation":
        return result.returncode == 0, result.stderr, result.returncode
    if result.returncode != 0:
        return False, result.stderr, result.returncode
    ok, detail = check_assertions(result.stdout)
    return ok, detail, result.returncode


def chapter_from_path(path: str) -> str:
    for part in Path(path).parts:
        if part.startswith("chapter-"):
            return part
    return Path(path).parent.name


def _aggregate_chapters(
    results: list[dict[str, Any]],
) -> list[tuple[str, str, str]]:
    chapters: defaultdict[str, dict[str, int]] = defaultdict(
        lambda: {"total": 0, "failed": 0},
    )
    for r in results:
        bucket = chapters[r["chapter"]]
        bucket["total"] += 1
        if r["status"] != "pass":
            bucket["failed"] += 1
    rows: list[tuple[str, str, str]] = []
    for name in sorted(chapters, key=_natural_sort_key):
        c = chapters[name]
        display = name.removeprefix("chapter-")
        rows.append((display, str(c["total"]), str(c["failed"])))
    return rows


def print_chapter_breakdown(results: list[dict[str, Any]]) -> None:
    rows = _aggregate_chapters(results)
    headers = ("Clause", "# of tests", "Failed")
    widths = [
        max(len(h), max((len(row[i]) for row in rows), default=0))
        for i, h in enumerate(headers)
    ]

    def _border(left: str, mid: str, right: str) -> str:
        return left + mid.join("─" * (w + 2) for w in widths) + right

    def _row(
        vals: tuple[str, ...] | list[str],
        aligns: list[str],
        color: str = "",
    ) -> str:
        cells = [f" {v:{a}{widths[i]}} " for i, (v, a) in enumerate(zip(vals, aligns))]
        inner = "│".join(cells)
        return f"│{color}{inner}{RESET}│" if color else "│" + inner + "│"

    print("\nPer-chapter breakdown:")
    print(_border("┌", "┬", "┐"))
    print(_row(headers, ["<"] * 3))
    print(_border("├", "┼", "┤"))
    for row in rows:
        color = GREEN if row[2] == "0" else RED
        print(_row(row, ["<", ">", ">"], color))
    print(_border("└", "┴", "┘"))


def write_junit_xml(
    results: list[dict[str, Any]], elapsed: float, filepath: str,
) -> None:
    total = len(results)
    failures = sum(1 for r in results if r["status"] == "fail")
    errors = sum(1 for r in results if r["status"] == "timeout")

    suite = ET.Element(
        "testsuite",
        name="sv-tests",
        tests=str(total),
        failures=str(failures),
        errors=str(errors),
        time=f"{elapsed:.3f}",
    )

    for r in results:
        tc = ET.SubElement(
            suite,
            "testcase",
            name=r["name"],
            classname=r["chapter"],
            time=f"{r['time']:.3f}",
        )
        if r["status"] == "fail":
            ET.SubElement(
                tc,
                "failure",
                message=f"{r['name']} failed lint",
            ).text = r.get("stderr", "")
        elif r["status"] == "timeout":
            ET.SubElement(
                tc,
                "error",
                message=f"{r['name']} timed out",
            ).text = "Process exceeded 30s timeout."

    tree = ET.ElementTree(suite)
    ET.indent(tree, space="  ")
    tree.write(filepath, xml_declaration=True, encoding="unicode")


_SUBCLAUSE_RE = re.compile(r"\(§(\d+(?:\.\d+)*)\)")


def reported_subclauses(stderr: str) -> list[str]:
    return _SUBCLAUSE_RE.findall(stderr)


_CLAUSE_PREFIX_RE = re.compile(r"(\d+(?:\.\d+)*)--")

_CLAUSE_OF_MISTAGGED_FILE: dict[str, str] = {
    "9.3.3--fork_return.sv": "9.3.2",
    "13.4.4--fork-invalid.sv": "13.4",
    "18.9--controlling-constraints-with-constraint_mode_1.sv": "18.9",
    "18.17.2--if-else-production-statements_0_fail.sv": "23.9",
    "18.17.2--if-else-production-statements_2_fail.sv": "23.9",
    "18.17.3--case-production-statements_0_fail.sv": "23.9",
    "18.17.6--aborting-productions-break-and-return_2_fail.sv": "18.17",
}

_RULE_OF_FILE_TAGGED_BY_FEATURE: dict[str, str] = {
    "variable-slice-zero.sv": "11.5.1",
}

_CLAUSE_OF_FILE = _CLAUSE_OF_MISTAGGED_FILE | _RULE_OF_FILE_TAGGED_BY_FEATURE


def tagged_clause(metadata: dict[str, str], name: str) -> str:
    if name in _CLAUSE_OF_FILE:
        return _CLAUSE_OF_FILE[name]
    tags = metadata.get("tags", "").split()
    if tags and re.fullmatch(r"\d+(?:\.\d+)*", tags[0]):
        return tags[0]
    prefix = _CLAUSE_PREFIX_RE.match(name)
    return prefix.group(1) if prefix else ""


_SUBCLAUSE_OF_TAG: dict[str, str] = {
    "7.4.3": "7.4.6",
    "7.4.4": "7.4.3",
    "7.4.5": "7.4.4",
    "18.5.3": "11.4.13",
    "18.5.4": "18.5.3",
    "18.5.5": "18.5.4",
    "18.5.6": "18.5.5",
    "18.5.7": "18.5.6",
    "18.5.8.1": "18.5.7.1",
    "18.5.8.2": "18.5.7.2",
    "18.5.9": "18.5.8",
    "18.5.10": "18.5.9",
    "18.5.11": "18.5.10",
    "18.5.12": "18.5.11",
    "18.5.13": "18.5.12",
    "18.5.14": "18.5.13",
    "18.5.14.1": "18.5.13.1",
    "18.5.14.2": "18.5.13.2",
    "20.14": "20.13",
    "20.15": "20.14",
}


def subclause_of_tag(tag: str) -> str:
    return _SUBCLAUSE_OF_TAG.get(tag, tag)


def subclause_is_within(reported: str, clause: str) -> bool:
    clause_parts = clause.split(".")
    return reported.split(".")[: len(clause_parts)] == clause_parts


def _rejection_matches_tag(stderr: str, tag: str) -> bool:
    if not tag:
        return True
    reported = reported_subclauses(stderr)
    if not reported:
        return True
    clause = subclause_of_tag(tag)
    return any(subclause_is_within(r, clause) for r in reported)


def _run_and_evaluate(
    path: str, metadata: dict[str, str], library: Library,
) -> tuple[str, str, int, int]:
    ok, stderr, returncode = run_test(
        path,
        mode=run_mode(metadata),
        defines=metadata.get("defines", "").split(),
        library=library,
    )
    if metadata.get("should_fail_because"):
        ok = (
            returncode == 1
            and bool(stderr.strip())
            and _rejection_matches_tag(
                stderr, tagged_clause(metadata, Path(path).name),
            )
        )
    return "pass" if ok else "fail", stderr, int(ok), returncode


def _tag_prefixed(name: str, metadata: dict[str, str]) -> str:
    tags = metadata.get("tags", "").split()
    if tags and not re.match(r"^\d+\.", name):
        return f"{tags[0]}--{name}"
    return name


def build_result(
    path: str, libraries: dict[str, Library] | None = None,
) -> tuple[dict[str, Any], int]:
    chapter = chapter_from_path(path)
    try:
        name = str(Path(path).relative_to(TEST_DIR / chapter))
    except ValueError:
        name = Path(path).name

    try:
        metadata = parse_metadata(path)
        name = _tag_prefixed(name, metadata)
        should_fail = bool(metadata.get("should_fail_because"))
        clause = tagged_clause(metadata, Path(path).name)
        library = library_for(metadata, libraries or {})

        t0 = time.monotonic()
        returncode: int | None = None
        try:
            status, stderr, ok_int, returncode = _run_and_evaluate(
                path, metadata, library,
            )
        except subprocess.TimeoutExpired:
            status, stderr, ok_int = "timeout", "", 0
        dt = time.monotonic() - t0
    except (OSError, subprocess.SubprocessError, ValueError) as exc:
        print(
            f"error: {name}: {type(exc).__name__}: {exc}",
            file=sys.stderr,
            flush=True,
        )
        return {
            "name": name,
            "chapter": chapter,
            "status": "fail",
            "time": 0.0,
            "stderr": f"{type(exc).__name__}: {exc}",
            "should_fail": False,
            "returncode": None,
            "clause": "",
        }, 0

    return {
        "name": name,
        "chapter": chapter,
        "status": status,
        "time": dt,
        "stderr": stderr,
        "should_fail": should_fail,
        "returncode": returncode,
        "clause": clause,
    }, ok_int


def print_reason(result: dict[str, Any]) -> None:
    if result["status"] == "pass" and not result.get("should_fail"):
        return
    for line in result.get("stderr", "").splitlines():
        print(f"    {line}", flush=True)
    if not result.get("should_fail") or result["status"] != "fail":
        return
    tag = result.get("clause", "")
    clause = subclause_of_tag(tag)
    reported = reported_subclauses(result.get("stderr", ""))
    if tag and reported and not any(
        subclause_is_within(r, clause) for r in reported
    ):
        named = f"tag {tag} names" if clause != tag else "tag names"
        print(
            f"    deltahdl rejected the code under §{', §'.join(reported)}, but the"
            f" test's {named} §{clause}",
            flush=True,
        )
        return
    if result.get("returncode") not in (0, None):
        print(
            f"    deltahdl exited {result['returncode']} without rejecting the code",
            flush=True,
        )


def print_status(result: dict[str, Any], ok_int: int) -> None:
    if result["status"] == "timeout":
        print(f"  {RED}TIMEOUT{RESET}: {result['name']}", flush=True)
    else:
        print_result(bool(ok_int), result["name"])
    print_reason(result)


def suite_revision() -> str:
    try:
        result = subprocess.run(
            ["git", "-C", str(TEST_DIR), "rev-parse", "HEAD"],
            capture_output=True,
            timeout=30,
            check=False,
            text=True,
        )
    except OSError:
        return "unknown"
    if result.returncode != 0:
        return "unknown"
    return result.stdout.strip()


def _libraries_or_exit() -> dict[str, Library]:
    try:
        return load_libraries()
    except (OSError, ValueError, KeyError) as exc:
        print(f"error: {type(exc).__name__}: {exc}", file=sys.stderr)
        sys.exit(1)


def _run_all(
    build: Callable[[str], tuple[dict[str, Any], int]], tests: list[str],
) -> tuple[list[dict[str, Any]], list[int]]:
    results: list[dict[str, Any]] = []
    ok_flags: list[int] = []
    try:
        with ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
            for result, ok in pool.map(build, tests):
                results.append(result)
                ok_flags.append(ok)
                print_status(result, ok)
    except BrokenPipeError:
        raise
    except (OSError, subprocess.SubprocessError, RuntimeError) as exc:
        print(
            f"\nerror: pool.map failed after {len(results)}/{len(tests)} "
            f"results: {type(exc).__name__}: {exc}",
            file=sys.stderr,
            flush=True,
        )
    return results, ok_flags


def _print_summary(results: list[dict[str, Any]], passed: int) -> None:
    failed = len(results) - passed
    pct = 100.0 * passed / len(results) if results else 0.0
    print(
        f"\nsv-tests revision: {suite_revision()}"
        f"\nsv-tests summary: {passed}/{len(results)} passed ({pct:.1f}%), "
        f"{failed} failed",
        flush=True,
    )
    print_chapter_breakdown(results)
    sys.stdout.flush()


def _report_broken_pipe() -> None:
    devnull = os.open(os.devnull, os.O_WRONLY)
    os.dup2(devnull, sys.stdout.fileno())
    os.close(devnull)
    print(
        "\nerror: stdout pipe broke — the GitHub Actions runner likely"
        " killed the reader before output was fully drained."
        "\nThis is a known runner bug: the .NET runtime sets"
        " SIGPIPE=SIG_IGN (inherited by all child processes), and"
        "\nProcessInvoker.cs has a 5-second hard timeout that kills"
        " the process tree if stdout is not drained in time."
        "\nOn macOS with 16 KB pipe buffers this deadline is"
        " regularly missed."
        "\nSee: https://github.com/actions/runner/issues/2684"
        "\nSee: https://github.com/actions/runner/blob/main/src/"
        "Runner.Worker/Handlers/NodeScriptActionHandler.cs"
        " (ProcessInvoker)",
        file=sys.stderr,
        flush=True,
    )


def main() -> None:
    args = parse_args()

    check_binary()

    tests = collect_tests(chapter=args.chapter)
    if not tests:
        print(f"error: no .sv files found in {TEST_DIR}", file=sys.stderr)
        sys.exit(1)

    build = partial(build_result, libraries=_libraries_or_exit())
    suite_start = time.monotonic()

    try:
        results, ok_flags = _run_all(build, tests)
        passed = sum(ok_flags)
        _print_summary(results, passed)
    except BrokenPipeError:
        _report_broken_pipe()
        sys.exit(1)

    if args.junit_xml:
        write_junit_xml(results, time.monotonic() - suite_start, args.junit_xml)
        print(f"\nJUnit XML written to {args.junit_xml}", flush=True)

    sys.exit(min(len(results) - passed, 1))
