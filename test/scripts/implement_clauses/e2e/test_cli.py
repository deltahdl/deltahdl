"""End-to-end tests for the implement_clauses CLI."""

from lib.python.test_utils import (
    build_base_env,
    install_fake_package,
    invoke_module,
)


# ---- Helpers ---------------------------------------------------------------


def _env(tmp_path, exit_code=0):
    """Build subprocess env with fake implement_clause."""
    fake_scripts = install_fake_package(
        tmp_path, "implement_clause", exit_code=exit_code,
    )
    return build_base_env(tmp_path, fake_scripts, "")


def _invoke(*args, cwd=None, env=None):
    """Run implement_clauses in a child process."""
    return invoke_module("implement_clauses", *args, cwd=cwd, env=env)


def _create_lrm(tmp_path):
    """Create and return a dummy LRM file path."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return str(lrm)


def _all_flags(tmp_path, clauses="15=17,16=18"):
    """Return the full set of required CLI flags."""
    return [
        "--lrm", _create_lrm(tmp_path),
        "--clauses", clauses,
        "--organization", "o",
        "--repo", "r",
    ]


# ---- Tests -----------------------------------------------------------------


def test_help_exits_zero():
    """--help exits with code 0."""
    assert _invoke("--help").returncode == 0


def test_help_shows_clauses():
    """--help output mentions --clauses."""
    assert "--clauses" in _invoke("--help").stdout


def test_missing_lrm_exits_nonzero(tmp_path):
    """Non-existent LRM file exits with non-zero code."""
    result = _invoke(
        "--lrm", str(tmp_path / "no.pdf"),
        "--clauses", "15=17",
        "--organization", "o",
        "--repo", "r",
    )
    assert result.returncode != 0


def test_invalid_clauses_exits_nonzero(tmp_path):
    """Invalid clause format exits with non-zero code."""
    assert _invoke(*_all_flags(tmp_path, clauses="bad=17")).returncode != 0


def test_successful_run(tmp_path):
    """Successful run exits with code 0."""
    env = _env(tmp_path)
    assert _invoke(*_all_flags(tmp_path), env=env).returncode == 0


def test_clause_failure_propagates(tmp_path):
    """Non-zero exit from implement_clause propagates."""
    env = _env(tmp_path, exit_code=1)
    assert _invoke(*_all_flags(tmp_path), env=env).returncode != 0
