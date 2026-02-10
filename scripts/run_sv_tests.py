#!/usr/bin/env python3
"""Run CHIPS Alliance sv-tests against deltahdl (advisory)."""

import argparse
import ast
import glob
import operator
import os
import re
import subprocess
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from xml.etree import ElementTree as ET

from test_common import BINARY, GREEN, RED, REPO_ROOT, RESET, check_binary, print_result

TEST_DIR = REPO_ROOT / "third_party" / "sv-tests" / "tests"


def parse_args():
    """Parse command-line arguments."""
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


def _natural_sort_key(text):
    """Split text into (str, int, str, int, ...) for natural ordering."""
    return [int(tok) if tok.isdigit() else tok for tok in re.split(r"(\d+)", text)]


def collect_tests(chapter=None):
    """Collect .sv files under the chapter directories.

    If *chapter* is given (e.g. "5"), only that chapter's tests are collected.
    """
    chapter_glob = f"chapter-{chapter}" if chapter else "chapter-*"
    pattern = str(TEST_DIR / chapter_glob / "*.sv")
    return sorted(glob.glob(pattern), key=_natural_sort_key)


def parse_metadata(path):
    """Parse sv-tests metadata from a .sv file header comment."""
    text = Path(path).read_text(encoding="utf-8")
    match = re.search(r"/\*(.*?)\*/", text, re.DOTALL)
    if not match:
        return {}
    metadata = {}
    for line in match.group(1).splitlines():
        m = re.match(r"\s*:(\w+):\s*(.*)", line)
        if m:
            metadata[m.group(1)] = m.group(2).strip()
    return metadata


_COMPARE_OPS = {
    ast.Eq: operator.eq,
    ast.NotEq: operator.ne,
    ast.Lt: operator.lt,
    ast.LtE: operator.le,
    ast.Gt: operator.gt,
    ast.GtE: operator.ge,
    ast.In: lambda a, b: operator.contains(b, a),
    ast.NotIn: lambda a, b: not operator.contains(b, a),
}


def eval_node(node):
    """Evaluate an AST node containing only constants and comparisons."""
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
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return not eval_node(node.operand)
    raise ValueError(f"Unsupported node: {type(node).__name__}")


def check_assertions(stdout):
    """Evaluate :assert: patterns in simulation output."""
    for line in stdout.splitlines():
        match = re.search(r":assert:\s*(.*)", line)
        if not match:
            continue
        expr = match.group(1).strip()
        try:
            tree = ast.parse(expr, mode="eval")
            if not eval_node(tree.body):
                return False, f"Assertion failed: {expr}"
        except (SyntaxError, ValueError) as exc:
            return False, f"Assertion error: {expr}: {exc}"
    return True, ""


def run_test(path, simulate=False, defines=()):
    """Run deltahdl on a single .sv file.

    Returns (passed, stderr_or_detail) tuple.
    """
    cmd = [str(BINARY)] if simulate else [str(BINARY), "--lint-only"]
    for d in defines:
        cmd.extend(["-D", d])
    cmd.append(path)
    result = subprocess.run(
        cmd,
        capture_output=True,
        timeout=30,
        check=False,
        text=True,
    )
    if not simulate:
        return result.returncode == 0, result.stderr
    if result.returncode != 0:
        return False, result.stderr
    return check_assertions(result.stdout)


def chapter_from_path(path):
    """Extract the chapter directory name (e.g. 'chapter-5') from a path."""
    return Path(path).parent.name


def _aggregate_chapters(results):
    """Aggregate results into sorted (name, passed, total, pct) row tuples."""
    chapters = defaultdict(lambda: {"passed": 0, "failed": 0})
    for r in results:
        bucket = chapters[r["chapter"]]
        if r["status"] == "pass":
            bucket["passed"] += 1
        else:
            bucket["failed"] += 1
    rows = []
    for name in sorted(chapters, key=_natural_sort_key):
        c = chapters[name]
        total = c["passed"] + c["failed"]
        pct = 100.0 * c["passed"] / total if total else 0.0
        display = name.removeprefix("chapter-")
        rows.append((display, str(c["passed"]), str(total), f"{pct:.1f}%"))
    return rows


def print_chapter_breakdown(results):
    """Print per-chapter pass/fail summary as a box-drawing table."""
    rows = _aggregate_chapters(results)
    headers = ("Chapter", "Passed", "Sub-Total", "Percentage")
    widths = [
        max(len(h), max((len(row[i]) for row in rows), default=0))
        for i, h in enumerate(headers)
    ]

    def _border(left, mid, right):
        return left + mid.join("─" * (w + 2) for w in widths) + right

    def _row(vals, aligns, color=""):
        cells = [f" {v:{a}{widths[i]}} " for i, (v, a) in enumerate(zip(vals, aligns))]
        inner = "│".join(cells)
        return f"│{color}{inner}{RESET}│" if color else "│" + inner + "│"

    print("\nPer-chapter breakdown:")
    print(_border("┌", "┬", "┐"))
    print(_row(headers, ["<"] * 4))
    print(_border("├", "┼", "┤"))
    for row in rows:
        color = GREEN if row[3] == "100.0%" else RED
        print(_row(row, ["<", ">", ">", ">"], color))
    print(_border("└", "┴", "┘"))


def write_junit_xml(results, elapsed, filepath):
    """Write JUnit XML report to the given filepath."""
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


def build_result(path):
    """Run one sv-test and return (result_dict, ok_int). Does not print."""
    name = Path(path).name
    chapter = chapter_from_path(path)
    metadata = parse_metadata(path)
    simulate = "simulation" in metadata.get("type", "").split()
    should_fail = bool(metadata.get("should_fail_because"))
    defines = metadata.get("defines", "").split()

    t0 = time.monotonic()
    stderr = ""
    try:
        ok, stderr = run_test(path, simulate=simulate, defines=defines)
        dt = time.monotonic() - t0
        if should_fail:
            ok = not ok
        status = "pass" if ok else "fail"
        ok_int = int(ok)
    except subprocess.TimeoutExpired:
        dt = time.monotonic() - t0
        status = "timeout"
        ok_int = 0

    return {
        "name": name,
        "chapter": chapter,
        "status": status,
        "time": dt,
        "stderr": stderr,
    }, ok_int


def print_status(result, ok_int):
    """Print PASS/FAIL/TIMEOUT for a single test result."""
    if result["status"] == "timeout":
        print(f"  {RED}TIMEOUT{RESET}: {result['name']}", flush=True)
    else:
        print_result(bool(ok_int), result["name"])


def execute_single_test(path):
    """Run one sv-test, print result, and return (result_dict, ok_int)."""
    result, ok_int = build_result(path)
    print_status(result, ok_int)
    return result, ok_int


def main():
    """Run all sv-tests and print a summary."""
    args = parse_args()

    check_binary()

    tests = collect_tests(chapter=args.chapter)
    if not tests:
        print(f"error: no .sv files found in {TEST_DIR}", file=sys.stderr)
        sys.exit(1)

    results = []
    passed = 0
    suite_start = time.monotonic()

    with ThreadPoolExecutor(max_workers=os.cpu_count()) as pool:
        for result, ok in pool.map(build_result, tests):
            print_status(result, ok)
            results.append(result)
            passed += ok

    failed = len(results) - passed
    pct = 100.0 * passed / len(results)
    print(f"\nsv-tests summary: {passed}/{len(results)} passed ({pct:.1f}%), {failed} failed")

    print_chapter_breakdown(results)

    if args.junit_xml:
        elapsed = time.monotonic() - suite_start
        write_junit_xml(results, elapsed, args.junit_xml)
        print(f"\nJUnit XML written to {args.junit_xml}")

    sys.exit(min(failed, 1))


if __name__ == "__main__":  # pragma: no cover
    main()
