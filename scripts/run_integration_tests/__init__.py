import re
import subprocess
import sys
from pathlib import Path

from lib.python.run_tests_common import (
    BINARY, REPO_ROOT, check_assertions, check_binary, parse_metadata,
    print_result, reported_subclauses, subclause_is_within,
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


def subclause_of(metadata: dict[str, str], sv_path: Path) -> str:
    subclause = metadata.get("subclause", "")
    if not _SUBCLAUSE_TEXT.fullmatch(subclause):
        msg = f"{sv_path.name}: expected a :subclause: header, got {subclause!r}"
        raise ValueError(msg)
    return subclause


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

    passed = 0
    failed = 0
    for sv_path in tests:
        ok, detail = run_test(sv_path)
        print_result(ok, sv_path.stem)
        passed += ok
        failed += not ok
        for line in detail.splitlines():
            print(f"    {line}")

    total = passed + failed
    print(
        f"\nintegration-tests summary: {passed}/{total} passed, {failed} failed",
    )
    sys.exit(min(failed, 1))
