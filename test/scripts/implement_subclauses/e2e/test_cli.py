"""End-to-end tests for the implement_subclauses CLI."""

from lib.python.test_utils import (
    build_base_env,
    install_fake_gh,
    install_fake_package,
    invoke_module,
)


# ---- Helpers ---------------------------------------------------------------


def _env(tmp_path, exit_code=0):
    """Build subprocess env with fake implement_subclause and gh."""
    fake_scripts = install_fake_package(
        tmp_path, "implement_subclause", exit_code=exit_code,
    )
    title = (
        "Ensure IEEE 1800-2023 §6.1"
        " functionalities and tests are implemented and properly named"
    )
    fake_bin = install_fake_gh(tmp_path, issue_title=title)
    return build_base_env(tmp_path, fake_scripts, fake_bin)


def _invoke(*args, cwd=None, env=None):
    """Run implement_subclauses in a child process."""
    return invoke_module("implement_subclauses", *args, cwd=cwd, env=env)


def _all_flags(tmp_path):
    """Return the full set of required CLI flags."""
    return [
        "--lrm", str(tmp_path / "lrm.pdf"),
        "--issues", "100,101",
        "--organization", "o",
        "--repo", "r",
    ]


# ---- Tests -----------------------------------------------------------------


def test_help_exits_zero():
    """--help exits with code 0."""
    assert _invoke("--help").returncode == 0


def test_help_shows_issues():
    """--help output mentions --issues."""
    assert "--issues" in _invoke("--help").stdout


def test_missing_lrm_exits_nonzero(tmp_path):
    """Non-existent LRM file exits with non-zero code."""
    result = _invoke(
        "--lrm", str(tmp_path / "no.pdf"),
        "--issues", "100",
        "--organization", "o",
        "--repo", "r",
    )
    assert result.returncode != 0


def test_successful_run(tmp_path):
    """Successful run exits with code 0."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    env = _env(tmp_path)
    result = _invoke(*_all_flags(tmp_path), env=env)
    assert result.returncode == 0


def test_prints_invoking_message(tmp_path):
    """Stdout contains the subclause being invoked."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    env = _env(tmp_path)
    result = _invoke(*_all_flags(tmp_path), env=env)
    assert "Invoking implement_subclause for 6.1" in result.stdout
