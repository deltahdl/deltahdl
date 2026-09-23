import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

from lib.python.run_tests_common import (
    BINARY, REPO_ROOT, check_assertions, check_binary, parse_metadata,
    print_clause_breakdown, print_result, reported_subclauses,
    subclause_is_within,
)

TEST_DIR = REPO_ROOT / "test" / "src" / "integration"

_OPTION_OF_STAGE: dict[str, str | None] = {
    "simulation": None,
    "elaboration": "--lint-only",
    "parsing": "--parse-only",
}

_SUBCLAUSE_TEXT = re.compile(r"\d+(?:\.\d+)*")

_ASSERT_LINE = re.compile(r":assert:")


def collect_tests() -> list[Path]:
    return sorted(TEST_DIR.glob("*.sv"))


def numbered_subclause(metadata: dict[str, str]) -> str:
    subclause = metadata.get("subclause", "")
    return subclause if _SUBCLAUSE_TEXT.fullmatch(subclause) else ""


def subclause_of(metadata: dict[str, str], sv_path: Path) -> str:
    subclause = numbered_subclause(metadata)
    if not subclause:
        msg = (
            f"{sv_path.name}: expected a :subclause: header,"
            f" got {metadata.get('subclause', '')!r}"
        )
        raise ValueError(msg)
    return subclause


def result_name(subclause: str, sv_path: Path) -> str:
    return f"{subclause}--{sv_path.name}" if subclause else sv_path.name


def clause_row(subclause: str) -> str:
    return subclause.split(".")[0] or "none"


def stage_option(metadata: dict[str, str], sv_path: Path) -> str | None:
    stage = metadata.get("stage", "")
    if stage not in _OPTION_OF_STAGE:
        msg = (
            f"{sv_path.name}: expected a :stage: header naming one of"
            f" {', '.join(_OPTION_OF_STAGE)}, got {stage!r}"
        )
        raise ValueError(msg)
    return _OPTION_OF_STAGE[stage]


def rejection_outcome(
    result: subprocess.CompletedProcess[str], subclause: str,
) -> tuple[bool, str]:
    if result.returncode != 1:
        return False, (
            f"expected deltahdl to reject the code, it exited"
            f" {result.returncode}\n{result.stderr}"
        )
    if any(
        subclause_is_within(reported, subclause)
        for reported in reported_subclauses(result.stderr)
    ):
        return True, ""
    return False, (
        f"expected a rejection under §{subclause}, got:\n{result.stderr}"
    )


def acceptance_outcome(
    result: subprocess.CompletedProcess[str], option: str | None,
) -> tuple[bool, str]:
    if result.returncode != 0:
        return False, f"exited {result.returncode}\n{result.stderr}"
    if option is not None:
        return True, ""
    if not _ASSERT_LINE.search(result.stdout):
        return False, "the simulation printed no :assert: line"
    return check_assertions(result.stdout)


def run_test(sv_path: Path) -> tuple[bool, str]:
    metadata = parse_metadata(str(sv_path))
    try:
        subclause = subclause_of(metadata, sv_path)
        option = stage_option(metadata, sv_path)
    except ValueError as exc:
        return False, str(exc)
    command = [str(BINARY)] if option is None else [str(BINARY), option]
    try:
        result = subprocess.run(
            [*command, str(sv_path)],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    if metadata.get("should_fail_because"):
        return rejection_outcome(result, subclause)
    return acceptance_outcome(result, option)


def main() -> None:
    check_binary()

    tests = collect_tests()
    if not tests:
        print(f"error: no .sv files found in {TEST_DIR}", file=sys.stderr)
        sys.exit(1)

    failed_by_clause: defaultdict[str, int] = defaultdict(int)
    for sv_path in tests:
        subclause = numbered_subclause(parse_metadata(str(sv_path)))
        ok, detail = run_test(sv_path)
        print_result(ok, result_name(subclause, sv_path))
        failed_by_clause[clause_row(subclause)] += not ok
        for line in detail.splitlines():
            print(f"    {line}")

    total = len(tests)
    failed = sum(failed_by_clause.values())
    passed = total - failed
    print(
        f"\nintegration-tests summary: {passed}/{total} passed"
        f" ({100.0 * passed / total:.1f}%), {failed} failed",
    )
    print_clause_breakdown(dict(failed_by_clause))
    sys.exit(min(failed, 1))
