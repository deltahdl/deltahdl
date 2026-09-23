import argparse
import glob
import json
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
    BINARY, RED, REPO_ROOT, RESET, check_assertions, check_binary,
    natural_sort_key, parse_metadata, print_clause_breakdown, print_result,
    reported_subclauses, subclause_is_within,
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


def collect_tests(chapter: str | None = None) -> list[str]:
    chapter_glob = f"chapter-{chapter}" if chapter else "chapter-*"
    pattern = str(TEST_DIR / chapter_glob / "**" / "*.sv")
    return sorted(glob.glob(pattern, recursive=True), key=natural_sort_key)


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


def failed_by_clause(results: list[dict[str, Any]]) -> dict[str, int]:
    failed: defaultdict[str, int] = defaultdict(int)
    for r in results:
        failed[r["chapter"].removeprefix("chapter-")] += int(r["status"] != "pass")
    return dict(failed)


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


_CLAUSE_PREFIX_RE = re.compile(r"(\d+(?:\.\d+)*)--")

_CLAUSE_OF_MISTAGGED_FILE: dict[str, str] = {
    "9.3.3--fork_return.sv": "9.3.2",
    "10.3--proc-assignment--bad.sv": "10.4",
    "13.4.4--fork-invalid.sv": "13.4",
    "18.9--controlling-constraints-with-constraint_mode_1.sv": "18.9",
    "18.17.2--if-else-production-statements_0_fail.sv": "23.9",
    "18.17.2--if-else-production-statements_2_fail.sv": "23.9",
    "18.17.3--case-production-statements_0_fail.sv": "23.9",
    "18.17.6--aborting-productions-break-and-return_2_fail.sv": "18.17",
}

_RULE_OF_FILE_TAGGED_BY_FEATURE: dict[str, str] = {
    "variable-slice-zero.sv": "11.5.1",
    "14.3--clocking-block-signals-error.sv": "10.4",
    "11.4.14.3--unpack_stream_inv.sv": "11.4.14",
}

_RULE_BROKEN_BY_FILE_THE_SUITE_EXPECTS_ACCEPTED: dict[str, str] = {
    "20.4--timeformat.sv": "20.4.3",
}

_CLAUSE_OF_FILE = (
    _CLAUSE_OF_MISTAGGED_FILE
    | _RULE_OF_FILE_TAGGED_BY_FEATURE
    | _RULE_BROKEN_BY_FILE_THE_SUITE_EXPECTS_ACCEPTED
)


def expects_rejection(metadata: dict[str, str], name: str) -> bool:
    return (
        bool(metadata.get("should_fail_because"))
        or name in _RULE_BROKEN_BY_FILE_THE_SUITE_EXPECTS_ACCEPTED
    )


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
    if expects_rejection(metadata, Path(path).name):
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
        should_fail = expects_rejection(metadata, Path(path).name)
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
    print_clause_breakdown(failed_by_clause(results))
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
