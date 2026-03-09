"""End-to-end tests for the classify_tests CLI."""

from lib.python.test_utils import (
    build_base_env,
    install_fake_package,
    install_fake_script,
    invoke_module,
)


# ---- Helpers ---------------------------------------------------------------


def _install_fake_classify_test(tmp_path, exit_code=0):
    """Install a fake classify_test package that exits with *exit_code*."""
    return install_fake_package(tmp_path, "classify_test", exit_code=exit_code)


def _base_env(tmp_path, fake_scripts_dir):
    """Build subprocess env with fake classify_test on PYTHONPATH."""
    fake_bin = install_fake_script(
        tmp_path, "true", "#!/bin/sh\nexit 0\n",
    )
    return build_base_env(tmp_path, fake_scripts_dir, fake_bin)


def _invoke(*args, cwd=None, env=None):
    """Run classify_tests in a child process."""
    return invoke_module("classify_tests", *args, cwd=cwd, env=env)


def _all_flags(tmp_path, tests="A,B"):
    """Return the full set of required CLI flags."""
    return [
        "--file", str(tmp_path / "test.cpp"),
        "--tests", tests,
        "--output-dir", str(tmp_path),
        "--lrm", str(tmp_path / "lrm.txt"),
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
    ]


def _run_batch(tmp_path, tests="A,B", exit_code=0):
    """Install fake classify_test and invoke classify_tests."""
    fake = _install_fake_classify_test(tmp_path, exit_code=exit_code)
    env = _base_env(tmp_path, fake)
    return _invoke(
        *_all_flags(tmp_path, tests=tests),
        cwd=str(tmp_path), env=env,
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage(tmp_path):
    """Running with no arguments prints usage to stderr."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "usage:" in _invoke(cwd=str(tmp_path), env=env).stderr


def test_usage_shows_classify_tests(tmp_path):
    """Usage line shows 'classify_tests' as program name."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "classify_tests" in _invoke(cwd=str(tmp_path), env=env).stderr


def test_missing_file_flag_reported(tmp_path):
    """Omitting --file reports the missing argument."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "--file" in _invoke(
        "--tests", "A", cwd=str(tmp_path), env=env,
    ).stderr


def test_missing_tests_flag_reported(tmp_path):
    """Omitting --tests reports the missing argument."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "--tests" in _invoke(
        "--file", "f.cpp", cwd=str(tmp_path), env=env,
    ).stderr


# ---- Successful run --------------------------------------------------------


def test_all_pass_exits_zero(tmp_path):
    """Exits 0 when all classify_test calls succeed."""
    assert _run_batch(tmp_path, tests="A,B").returncode == 0


def test_single_test_exits_zero(tmp_path):
    """Exits 0 with a single test."""
    assert _run_batch(tmp_path, tests="Only").returncode == 0


# ---- Failure ---------------------------------------------------------------


def test_failure_exits_nonzero(tmp_path):
    """Exits non-zero when classify_test fails."""
    assert _run_batch(tmp_path, tests="A", exit_code=1).returncode != 0


# ---- Progress output -------------------------------------------------------


def test_progress_output_format(tmp_path):
    """Progress lines show test index and name."""
    result = _run_batch(tmp_path, tests="A,B")
    assert "Processing test 1/2: A" in result.stdout


# ---- Optional flags --------------------------------------------------------


def test_dry_run_forwarded(tmp_path):
    """--dry-run flag is accepted and exits 0."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        *_all_flags(tmp_path), "--dry-run",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0


def test_no_commit_forwarded(tmp_path):
    """--no-commit flag is accepted and exits 0."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        *_all_flags(tmp_path), "--no-commit",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0


def test_issue_forwarded(tmp_path):
    """--issue flag is accepted and exits 0."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        *_all_flags(tmp_path), "--issue", "42",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0
