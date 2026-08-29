"""Run simulation e2e tests against deltahdl."""

import contextlib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from lib.python.run_tests_common import BINARY, REPO_ROOT, check_binary, print_result

TEST_DIR = REPO_ROOT / "test" / "src" / "e2e"

# What a .exit file may hold: one status, written as digits with an optional
# sign. The sign is admitted because run_test passes whatever it reads straight
# to a comparison against a returncode, and a platform is free to report a
# signal as a negative number there.
STATUS_TEXT = re.compile(r"[+-]?[0-9]+")

# The suffix of the file a case names an earlier command line in. A case whose
# subject takes two invocations of deltahdl has nowhere else to name the first
# one, because .args names the arguments of the invocation whose output
# .expected records.
BEFORE_SUFFIX = ".before"


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


def before_arguments(sv_path: Path) -> list[str] | None:
    """Return the arguments a case named in the .before file beside its source.

    A case whose subject is two invocations of deltahdl has nowhere else to
    name the first one, because .args names the arguments of the invocation
    whose output .expected records. §33.5.3's separate compilation is such a
    subject: one invocation compiles source descriptions into a library file,
    a second binds a design out of that file, and "it is essential that library
    cells persist, and the compiled forms shall, therefore, exist somewhere in
    the filesystem" is what puts a file between the two.

    The file holds one argument per line and a blank line names no argument,
    exactly as .args does, and the arguments go after the source path for the
    reason they go after it there. One file names one earlier invocation, which
    is what the separate compilation flow takes.

    Returns None where the file is absent, which leaves the case the single
    invocation every case was before this file existed.
    """
    before_path = sv_path.with_suffix(BEFORE_SUFFIX)
    if not before_path.exists():
        return None
    return [line for line in before_path.read_text().splitlines() if line]


def run_before(
    sv_path: Path, arguments: list[str], work_dir: str,
) -> str | None:
    """Run a case's earlier invocation and return what to report of a failure.

    Returns None where that invocation exited zero, which is what lets the
    invocation under test run. Returns text naming the .before file otherwise.
    Only the last invocation's output is compared to .expected, so a precompile
    that wrote no library file would otherwise be read through the bind that
    followed it: that bind reports a cell it cannot find, and that report says
    nothing about the invocation that actually failed.

    A timeout is reported like a non-zero status rather than raised, so a case
    whose earlier invocation hangs fails on its own rather than stopping every
    case after it.

    The invocation runs in `work_dir`, so a file it writes under a relative
    path lands there. deltahdl writes a precompiled library where its
    --precompile-out argument names it, and this module resolves every other
    file of a case beside the source under test/src/e2e/, so a library written
    beside the source would be a file `git status` reports and a later `git
    add` commits. `work_dir` is a directory run_test made outside the
    repository and removes when the case is over.
    """
    before_path = sv_path.with_suffix(BEFORE_SUFFIX)
    try:
        result = subprocess.run(
            [str(BINARY), str(sv_path), *arguments],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
            cwd=work_dir,
        )
    except subprocess.TimeoutExpired:
        return f"{before_path.name}: TIMEOUT"
    if result.returncode == 0:
        return None
    return (
        f"{before_path.name}: exited {result.returncode}\n"
        f"{visible_output(result)}"
    )


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
    .expected file is what makes the .sv file a case at all. Three further
    files of that stem are optional: .args names the arguments to pass after
    the source path, .exit names the status the run has to exit with, and
    .before names the arguments of an invocation to run before the one under
    test. A case that carries none of them is judged on its printed text alone.

    A case that names an earlier invocation fails on it where it stands, so
    that the report names that invocation rather than whatever the invocation
    under test made of what the earlier one did not leave behind. Both
    invocations of such a case run in one temporary directory, which is where a
    library file the earlier one writes lands. A case that names no earlier
    invocation runs where the runner itself was started, which is where every
    case ran before .before existed.

    The arguments go after the source path because deltahdl parses an option
    wherever it stands: ParseArgs in src/driver/cli_options.cpp loops over the
    whole of argv and imposes no order between an option and a source file.
    Putting them after leaves the source path in the position it has always
    held, which is the first one after the program name.

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

    before = before_arguments(sv_path)
    with contextlib.ExitStack() as stack:
        work_dir: str | None = None
        if before is not None:
            work_dir = stack.enter_context(tempfile.TemporaryDirectory())
            detail = run_before(sv_path, before, work_dir)
            if detail is not None:
                return False, detail
        try:
            result = subprocess.run(
                [str(BINARY), str(sv_path), *case_arguments(sv_path)],
                capture_output=True,
                text=True,
                timeout=30,
                check=False,
                cwd=work_dir,
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
