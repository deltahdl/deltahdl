"""End-to-end tests for the classify_tests CLI."""

import subprocess
from pathlib import Path

import pytest

from lib.python.test_utils import (
    build_base_env,
    e2e_base_flags,
    install_fake_package,
    install_fake_script,
    invoke_module,
)


# ---- Helpers ---------------------------------------------------------------


def _fresh_env(tmp_path: Path, exit_code: int = 0) -> dict[str, str]:
    """Install fake classify_test and return a subprocess env."""
    fake = install_fake_package(
        tmp_path, "classify_test", exit_code=exit_code,
    )
    fake_bin = install_fake_script(
        tmp_path, "true", "#!/bin/sh\nexit 0\n",
    )
    return build_base_env(tmp_path, fake, fake_bin)


def _invoke(
    *args: str,
    cwd: str | None = None,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run classify_tests in a child process."""
    return invoke_module("classify_tests", *args, cwd=cwd, env=env)


def _all_flags(tmp_path: Path, tests: str = "S.A,S.B") -> list[str]:
    """Return the full set of required CLI flags."""
    return [
        "--file", str(tmp_path / "test.cpp"),
        "--tests", tests,
        *e2e_base_flags(tmp_path),
    ]


def _run_batch(
    tmp_path: Path, tests: str = "S.A,S.B", exit_code: int = 0,
) -> subprocess.CompletedProcess[str]:
    """Install fake classify_test and invoke classify_tests."""
    env = _fresh_env(tmp_path, exit_code=exit_code)
    return _invoke(
        *_all_flags(tmp_path, tests=tests),
        cwd=str(tmp_path), env=env,
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage(tmp_path: Path) -> None:
    """Running with no arguments prints usage to stderr."""
    assert "usage:" in _invoke(
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


def test_usage_shows_classify_tests(tmp_path: Path) -> None:
    """Usage line shows 'classify_tests' as program name."""
    assert "classify_tests" in _invoke(
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


def test_missing_file_flag_reported(tmp_path: Path) -> None:
    """Omitting --file reports the missing argument."""
    assert "--file" in _invoke(
        "--tests", "A",
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


def test_missing_tests_flag_reported(tmp_path: Path) -> None:
    """Omitting --tests reports the missing argument."""
    assert "--tests" in _invoke(
        "--file", "f.cpp",
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


# ---- Successful run --------------------------------------------------------


def test_all_pass_exits_zero(tmp_path: Path) -> None:
    """Exits 0 when all classify_test calls succeed."""
    assert _run_batch(tmp_path, tests="S.A,S.B").returncode == 0


def test_single_test_exits_zero(tmp_path: Path) -> None:
    """Exits 0 with a single test."""
    assert _run_batch(tmp_path, tests="S.Only").returncode == 0


# ---- Failure ---------------------------------------------------------------


def test_failure_exits_nonzero(tmp_path: Path) -> None:
    """Exits non-zero when classify_test fails."""
    assert _run_batch(tmp_path, tests="S.A", exit_code=1).returncode != 0


# ---- Progress output -------------------------------------------------------


def test_progress_output_format(tmp_path: Path) -> None:
    """Progress lines show test index and name."""
    assert "Processing test 1/2: S.A" in _run_batch(tmp_path).stdout


# ---- Optional flags --------------------------------------------------------


@pytest.mark.parametrize("extra", [
    ["--dry-run"],
    ["--no-commit"],
    ["--issue", "42"],
], ids=["dry-run", "no-commit", "issue"])
def test_optional_flag_accepted(tmp_path: Path, extra: list[str]) -> None:
    """Optional flags are accepted and exit 0."""
    flags = list(_all_flags(tmp_path)) + extra
    env = _fresh_env(tmp_path)
    proc = _invoke(*flags, cwd=str(tmp_path), env=env)
    assert proc.returncode == 0
