"""Run simulation e2e tests against deltahdl."""

import os
import re
import subprocess
import sys
from pathlib import Path

from lib.python.run_tests_common import BINARY, REPO_ROOT, check_binary, print_result

TEST_DIR = REPO_ROOT / "test" / "src" / "e2e"

# What a .exit file may hold: one status, written as digits with an optional
# sign. The sign is admitted because run_test passes whatever it reads straight
# to a comparison against a returncode, and a platform is free to report a
# signal as a negative number there.
STATUS_TEXT = re.compile(r"[+-]?[0-9]+")


def visible_output(result: subprocess.CompletedProcess[str]) -> str:
    """Return what a user running deltahdl by hand would see on their terminal.

    A .expected file records this, so it records both streams. deltahdl writes
    a design's $display output to standard output and every diagnostic to
    standard error, so reading standard output alone leaves a source the tool
    rejects producing nothing to compare: such a case passes for as long as its
    .expected file is empty, whatever the tool reported and whether it reported
    anything at all. Standard output comes first because that is the order the
    two arrive in for a design that runs, and interleaving cannot be recovered
    from two captured pipes in any case.

    The absolute path of the repository is cut out of what comes back, because
    a diagnostic names the source file it stands in and the name deltahdl is
    given is the one the caller passed. That path is
    /home/runner/work/deltahdl/deltahdl/... on the Ubuntu jobs and
    /Users/runner/work/... on macos-26, so a .expected holding it could match
    on one runner only. What is left is the path relative to the repository,
    which is the same everywhere and is how the repository names a file
    anywhere else.
    """
    combined = f"{result.stdout}{result.stderr}"
    return combined.replace(f"{REPO_ROOT}{os.sep}", "")


def case_arguments(sv_path: Path) -> list[str]:
    """Return the arguments a case named in the .args file beside its source.

    A case whose subject is an option has nowhere else to name it, because the
    source path is otherwise the whole command line deltahdl is given. The file
    holds one argument per line, so an argument may hold a space without being
    quoted, and a blank line names no argument rather than an empty one.

    The file is optional and an absent one names no arguments, which runs
    deltahdl on the source path alone. That is what every case did before the
    file existed, so a case that carries only a .expected is unaffected.
    """
    args_path = sv_path.with_suffix(".args")
    if not args_path.exists():
        return []
    return [line for line in args_path.read_text().splitlines() if line]


def expected_status(sv_path: Path) -> int | None:
    """Return the status a case named in the .exit file beside its source.

    Comparing printed text alone passes a run that printed what it should and
    exited non-zero anyway, so a case whose subject is the exit status needs a
    file to name the status in. It holds that one number.

    Returns None where the file is absent, which leaves the case judged on its
    printed text alone.

    Raises ValueError where the file holds anything but a status, naming the
    file and the text found in it. int() raises on such a text already, but its
    message names neither, so the report a maintainer reads would point at this
    module and leave them to find which case carries the bad file.
    """
    status_path = sv_path.with_suffix(".exit")
    if not status_path.exists():
        return None
    text = status_path.read_text().strip()
    if not STATUS_TEXT.fullmatch(text):
        msg = f"{status_path}: expected an exit status, got {text!r}"
        raise ValueError(msg)
    return int(text)


def collect_tests() -> list[tuple[Path, Path]]:
    """Collect all .sv files that have a matching .expected file."""
    tests: list[tuple[Path, Path]] = []
    for sv in sorted(TEST_DIR.glob("*.sv")):
        expected = sv.with_suffix(".expected")
        if expected.exists():
            tests.append((sv, expected))
    return tests


def run_test(sv_path: Path, expected_path: Path) -> tuple[bool, str]:
    """Run deltahdl on a .sv file and compare what it printed to .expected.

    A case is a .sv file and a .expected file of the same stem, and the
    .expected file is what makes the .sv file a case at all. Two further files
    of that stem are optional: .args names the arguments to pass after the
    source path, and .exit names the status the run has to exit with. A case
    that carries neither is judged on its printed text alone.

    The arguments go after the source path because deltahdl parses an option
    wherever it stands: ParseArgs in src/main.cpp loops over the whole of argv
    and imposes no order between an option and a source file. Putting them
    after leaves the source path in the position it has always held, which is
    the first one after the program name.

    A .exit file the runner cannot read fails its own case and is reported like
    any other failure, rather than raising out of here and stopping every case
    after this one. The file is read before deltahdl is started, since a case
    whose own definition cannot be read is not worth a run.
    """
    expected_text = expected_path.read_text()
    try:
        status = expected_status(sv_path)
    except ValueError as exc:
        return False, str(exc)

    try:
        result = subprocess.run(
            [str(BINARY), str(sv_path), *case_arguments(sv_path)],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"

    actual = visible_output(result)
    if actual.rstrip("\n") != expected_text.rstrip("\n"):
        return False, f"expected:\n{expected_text}got:\n{actual}"
    if status is not None and result.returncode != status:
        return False, f"expected exit status {status}, got {result.returncode}"
    return True, ""


def main() -> None:
    """Run all simulation e2e tests and print a summary."""
    check_binary()

    tests = collect_tests()
    if not tests:
        print(f"error: no test pairs found in {TEST_DIR}", file=sys.stderr)
        sys.exit(1)

    passed = 0
    failed = 0
    for sv_path, expected_path in tests:
        name = sv_path.stem
        ok, detail = run_test(sv_path, expected_path)
        print_result(ok, name)
        passed += ok
        failed += not ok
        if detail:
            for line in detail.splitlines():
                print(f"    {line}")

    total = passed + failed
    print(f"\nsim-tests summary: {passed}/{total} passed, {failed} failed")
    sys.exit(min(failed, 1))
