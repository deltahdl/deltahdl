import contextlib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

from lib.python.run_tests_common import BINARY, REPO_ROOT, check_binary, print_result

TEST_DIR = REPO_ROOT / "test" / "src" / "e2e"

STATUS_TEXT = re.compile(r"[+-]?[0-9]+")

BEFORE_SUFFIX = ".before"

ARTIFACT_SUFFIX = ".artifact"
ARTIFACT_RECORD_SUFFIX = ".artifact.expected"

VCD_DATE_SECTION = re.compile(r"\$date\b.*?\$end\b", re.DOTALL)


def visible_output(result: subprocess.CompletedProcess[str]) -> str:
    combined = f"{result.stdout}{result.stderr}"
    return combined.replace(f"{REPO_ROOT}{os.sep}", "")


def case_arguments(sv_path: Path) -> list[str]:
    args_path = sv_path.with_suffix(".args")
    if not args_path.exists():
        return []
    return [line for line in args_path.read_text().splitlines() if line]


def before_arguments(sv_path: Path) -> list[str] | None:
    before_path = sv_path.with_suffix(BEFORE_SUFFIX)
    if not before_path.exists():
        return None
    return [line for line in before_path.read_text().splitlines() if line]


def run_before(
    sv_path: Path, arguments: list[str], work_dir: str,
) -> str | None:
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
    status_path = sv_path.with_suffix(".exit")
    if not status_path.exists():
        return None
    text = status_path.read_text().strip()
    if not STATUS_TEXT.fullmatch(text):
        msg = f"{status_path}: expected an exit status, got {text!r}"
        raise ValueError(msg)
    return int(text)


def artifact_name(sv_path: Path) -> Path | None:
    named = sv_path.with_suffix(ARTIFACT_SUFFIX)
    if not named.exists():
        return None
    lines = [line for line in named.read_text().splitlines() if line]
    if len(lines) != 1:
        msg = f"{named}: expected one file name, got {len(lines)}"
        raise ValueError(msg)
    return Path(lines[0])


def normalise_artifact(text: str) -> str:
    return VCD_DATE_SECTION.sub("$date $end", text)


def compare_artifact(sv_path: Path, artifact: Path, work_dir: str) -> str | None:
    record = sv_path.with_name(sv_path.stem + ARTIFACT_RECORD_SUFFIX)
    if not record.exists():
        return f"{record.name}: no recorded contents for {artifact}"
    written = Path(work_dir) / artifact
    if not written.exists():
        return f"{artifact}: the run wrote no such file"
    actual = normalise_artifact(written.read_text())
    recorded = normalise_artifact(record.read_text())
    if actual.rstrip("\n") == recorded.rstrip("\n"):
        return None
    return f"{artifact} expected:\n{recorded}got:\n{actual}"


def collect_tests() -> list[tuple[Path, Path]]:
    tests: list[tuple[Path, Path]] = []
    for sv in sorted(TEST_DIR.glob("*.sv")):
        expected = sv.with_suffix(".expected")
        if expected.exists():
            tests.append((sv, expected))
    return tests


def case_outcome(
    expected_text: str,
    result: subprocess.CompletedProcess[str],
    status: int | None,
    artifact_detail: str | None,
) -> tuple[bool, str]:
    actual = visible_output(result)
    if actual.rstrip("\n") != expected_text.rstrip("\n"):
        return False, f"expected:\n{expected_text}got:\n{actual}"
    if status is not None and result.returncode != status:
        return False, f"expected exit status {status}, got {result.returncode}"
    if artifact_detail is not None:
        return False, artifact_detail
    return True, ""


def run_test(sv_path: Path, expected_path: Path) -> tuple[bool, str]:
    expected_text = expected_path.read_text()
    try:
        status = expected_status(sv_path)
        artifact = artifact_name(sv_path)
    except ValueError as exc:
        return False, str(exc)

    before = before_arguments(sv_path)
    artifact_detail: str | None = None
    with contextlib.ExitStack() as stack:
        work_dir = ""
        if before is not None or artifact is not None:
            work_dir = stack.enter_context(tempfile.TemporaryDirectory())
        if before is not None:
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
                cwd=work_dir or None,
            )
        except subprocess.TimeoutExpired:
            return False, "TIMEOUT"
        if artifact is not None:
            artifact_detail = compare_artifact(sv_path, artifact, work_dir)

    return case_outcome(expected_text, result, status, artifact_detail)


def main() -> None:
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
