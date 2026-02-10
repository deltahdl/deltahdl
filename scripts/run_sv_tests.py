#!/usr/bin/env python3
"""Run CHIPS Alliance sv-tests against deltahdl (advisory)."""

import argparse
import glob
import re
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path
from xml.etree import ElementTree as ET

from test_common import BINARY, RED, REPO_ROOT, RESET, check_binary, print_result

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
    return parser.parse_args()


def _natural_sort_key(text):
    """Split text into (str, int, str, int, ...) for natural ordering."""
    return [int(tok) if tok.isdigit() else tok for tok in re.split(r"(\d+)", text)]


def collect_tests():
    """Collect all .sv files under the chapter directories."""
    pattern = str(TEST_DIR / "chapter-*" / "*.sv")
    return sorted(glob.glob(pattern), key=_natural_sort_key)


def run_test(path):
    """Run deltahdl --lint-only on a single .sv file.

    Returns (passed, stderr) tuple.
    """
    result = subprocess.run(
        [str(BINARY), "--lint-only", path],
        capture_output=True,
        timeout=30,
        check=False,
        text=True,
    )
    return result.returncode == 0, result.stderr


def chapter_from_path(path):
    """Extract the chapter directory name (e.g. 'chapter-5') from a path."""
    return Path(path).parent.name


def print_chapter_breakdown(results):
    """Print per-chapter pass/fail summary as a box-drawing table."""
    chapters = defaultdict(lambda: {"passed": 0, "failed": 0})
    for r in results:
        bucket = chapters[r["chapter"]]
        if r["status"] == "pass":
            bucket["passed"] += 1
        else:
            bucket["failed"] += 1

    names = sorted(chapters, key=_natural_sort_key)
    rows = []
    for name in names:
        c = chapters[name]
        total = c["passed"] + c["failed"]
        pct = 100.0 * c["passed"] / total if total else 0.0
        rows.append((name, str(c["passed"]), str(total), f"{pct:.1f}%"))

    headers = ("Chapter", "Passed", "Sub-Total", "Percentage")
    widths = [
        max(len(h), max((len(row[i]) for row in rows), default=0))
        for i, h in enumerate(headers)
    ]

    def _border(left, mid, right):
        return left + mid.join("─" * (w + 2) for w in widths) + right

    def _row(vals, aligns):
        cells = [f" {v:{a}{widths[i]}} " for i, (v, a) in enumerate(zip(vals, aligns))]
        return "│" + "│".join(cells) + "│"

    print("\nPer-chapter breakdown:")
    print(_border("┌", "┬", "┐"))
    print(_row(headers, ["<"] * 4))
    print(_border("├", "┼", "┤"))
    for row in rows:
        print(_row(row, ["<", ">", ">", ">"]))
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


def execute_single_test(path):
    """Run one sv-test and return (result_dict, passed_flag)."""
    name = Path(path).name
    chapter = chapter_from_path(path)
    t0 = time.monotonic()
    stderr = ""
    try:
        ok, stderr = run_test(path)
        dt = time.monotonic() - t0
        print_result(ok, name)
        status = "pass" if ok else "fail"
        ok_int = int(ok)
    except subprocess.TimeoutExpired:
        dt = time.monotonic() - t0
        status = "timeout"
        ok_int = 0
        print(f"  {RED}TIMEOUT{RESET}: {name}", flush=True)

    result = {
        "name": name,
        "chapter": chapter,
        "status": status,
        "time": dt,
        "stderr": stderr,
    }
    return result, ok_int


def main():
    """Run all sv-tests and print a summary."""
    args = parse_args()

    check_binary()

    tests = collect_tests()
    if not tests:
        print(f"error: no .sv files found in {TEST_DIR}", file=sys.stderr)
        sys.exit(1)

    results = []
    passed = 0
    suite_start = time.monotonic()

    for path in tests:
        result, ok = execute_single_test(path)
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
