"""End-to-end tests for the classify_files CLI."""

import os
import stat
import subprocess
import sys
from pathlib import Path

_SCRIPTS_DIR = str(
    Path(__file__).resolve().parents[4] / "scripts",
)


# ---- Helpers ---------------------------------------------------------------


def _install_fakes(tmp_path, exit_code=0):
    """Install fake classify_file and classify_test packages.

    Returns the directory to prepend to PYTHONPATH so the fakes
    shadow the real packages.
    """
    fake_scripts = tmp_path / "fake_scripts"
    # Fake classify_file
    fake_cf = fake_scripts / "classify_file"
    fake_cf.mkdir(parents=True)
    (fake_cf / "__init__.py").write_text("", encoding="utf-8")
    (fake_cf / "__main__.py").write_text(
        f"import sys; sys.exit({exit_code})\n",
        encoding="utf-8",
    )
    # Fake classify_test (needed for _github imports)
    fake_ct = fake_scripts / "classify_test"
    fake_ct.mkdir(parents=True)
    (fake_ct / "__init__.py").write_text("", encoding="utf-8")
    (fake_ct / "_github.py").write_text(
        "def fetch_issue_body(_org, _repo, _issue):\n"
        "    return '- [ ] a.cpp\\n- [ ] b.cpp\\n'\n"
        "\n"
        "def tick_checkbox(body, name):\n"
        "    return body.replace(\n"
        "        '- [ ] ' + name, '- [x] ' + name,\n"
        "    )\n"
        "\n"
        "def update_issue_body(_org, _repo, _issue, _body):\n"
        "    pass\n",
        encoding="utf-8",
    )
    return str(fake_scripts)


def _install_fake_gh(tmp_path, titles=None):
    """Install a fake gh that succeeds for all requests.

    *titles* maps issue number strings to title strings for
    ``--jq .title`` requests.
    """
    fake_bin = tmp_path / "fake_bin"
    fake_bin.mkdir(exist_ok=True)
    gh_script = fake_bin / "gh"
    title_cases = ""
    for number, title in (titles or {}).items():
        escaped = title.replace("'", "'\\''")
        title_cases += (
            f'  if echo "$@" | grep -q "issues/{number}"; then\n'
            f"    printf '%s' '{escaped}'\n"
            f'    exit 0\n'
            f'  fi\n'
        )
    gh_script.write_text(
        '#!/bin/sh\n'
        'for arg in "$@"; do\n'
        '  if [ "$arg" = ".title" ]; then\n'
        + title_cases +
        '    exit 1\n'
        '  fi\n'
        'done\n'
        'echo \'{"body": "- [ ] a.cpp\\n- [ ] b.cpp"}\'\n'
        'exit 0\n',
        encoding="utf-8",
    )
    gh_script.chmod(gh_script.stat().st_mode | stat.S_IEXEC)
    return str(fake_bin)


def _base_env(tmp_path, fake_scripts_dir, titles=None):
    """Build subprocess env with fake classify_file before real scripts."""
    env = os.environ.copy()
    env["HOME"] = str(tmp_path)
    pypath = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = os.pathsep.join(
        [fake_scripts_dir, _SCRIPTS_DIR]
        + ([pypath] if pypath else []),
    )
    fake_bin = _install_fake_gh(tmp_path, titles=titles)
    env["PATH"] = fake_bin + os.pathsep + env.get("PATH", "")
    return env


def _invoke(*args, cwd=None, env=None):
    """Run classify_files in a child process."""
    run_env = (env or os.environ).copy()
    if "PYTHONPATH" not in run_env:
        pypath = run_env.get("PYTHONPATH", "")
        run_env["PYTHONPATH"] = (
            _SCRIPTS_DIR + os.pathsep + pypath
            if pypath else _SCRIPTS_DIR
        )
    return subprocess.run(
        [sys.executable, "-m", "classify_files", *args],
        capture_output=True,
        text=True,
        cwd=cwd,
        env=run_env,
        check=False,
    )


def _all_flags(tmp_path):
    """Return the full set of required CLI flags."""
    return [
        "--files", "a.cpp,b.cpp",
        "--issue", "1",
        "--output-dir", str(tmp_path),
        "--lrm", str(tmp_path / "lrm.txt"),
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
    ]


def _all_flags_sub_issues(tmp_path):
    """Return CLI flags with --sub-issues instead of --files."""
    return [
        "--sub-issues", "1,2",
        "--issue", "1",
        "--output-dir", str(tmp_path),
        "--lrm", str(tmp_path / "lrm.txt"),
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
    ]


def _run_batch(tmp_path, exit_code=0):
    """Install fake classify_file and invoke classify_files."""
    fake = _install_fakes(tmp_path, exit_code=exit_code)
    env = _base_env(tmp_path, fake)
    return _invoke(
        *_all_flags(tmp_path),
        cwd=str(tmp_path), env=env,
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage(tmp_path):
    """Running with no arguments prints usage to stderr."""
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "usage:" in _invoke(cwd=str(tmp_path), env=env).stderr


def test_usage_shows_classify_files(tmp_path):
    """Usage line shows classify_files as program name."""
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "classify_files" in _invoke(
        cwd=str(tmp_path), env=env,
    ).stderr


def test_missing_files_flag_reported(tmp_path):
    """Omitting --files reports the missing argument."""
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "--files" in _invoke(
        "--issue", "1",
        "--output-dir", str(tmp_path),
        "--lrm", "lrm.txt",
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
        cwd=str(tmp_path), env=env,
    ).stderr


# ---- Successful batch run --------------------------------------------------


def test_batch_all_pass_exits_zero(tmp_path):
    """Exits 0 when all classify_file calls succeed."""
    assert _run_batch(tmp_path).returncode == 0


# ---- Failure batch run -----------------------------------------------------


def test_batch_failure_exits_one(tmp_path):
    """Exits 1 when classify_file fails."""
    assert _run_batch(tmp_path, exit_code=1).returncode == 1


# ---- Progress output -------------------------------------------------------


def test_batch_progress_output(tmp_path):
    """Progress lines show file index and name."""
    result = _run_batch(tmp_path)
    assert "Processing file 1/2: a.cpp" in result.stdout


# ---- --sub-issues ---------------------------------------------------------


def test_sub_issues_batch_exits_zero(tmp_path):
    """Exits 0 when --sub-issues is used and all pass."""
    titles = {
        "1": "Classify tests in a.cpp",
        "2": "Classify tests in b.cpp",
    }
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake, titles=titles)
    result = _invoke(
        *_all_flags_sub_issues(tmp_path),
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0


def test_dry_run_exits_zero(tmp_path):
    """--dry-run flag accepted and exits 0."""
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        *_all_flags(tmp_path), "--dry-run",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0


def test_no_commit_exits_zero(tmp_path):
    """--no-commit flag accepted and exits 0."""
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        *_all_flags(tmp_path), "--no-commit",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0


def test_both_flags_rejects(tmp_path):
    """--files and --sub-issues together are rejected."""
    fake = _install_fakes(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        "--files", "a.cpp",
        "--sub-issues", "1",
        "--issue", "1",
        "--output-dir", str(tmp_path),
        "--lrm", "lrm.txt",
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode != 0
