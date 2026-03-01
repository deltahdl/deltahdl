"""End-to-end tests for the classify_file CLI."""

import os
import stat
import subprocess
import sys
from pathlib import Path

_SCRIPTS_DIR = str(
    Path(__file__).resolve().parents[4] / "scripts",
)


# ---- Helpers ---------------------------------------------------------------


def _install_fake_classify_test(tmp_path, exit_code=0):
    """Install a fake classify_test package that exits with *exit_code*.

    Returns the directory to prepend to PYTHONPATH so the fake
    shadows the real classify_test.
    """
    fake_scripts = tmp_path / "fake_scripts"
    fake_pkg = fake_scripts / "classify_test"
    fake_pkg.mkdir(parents=True)
    (fake_pkg / "__init__.py").write_text("", encoding="utf-8")
    (fake_pkg / "__main__.py").write_text(
        f"import sys; sys.exit({exit_code})\n",
        encoding="utf-8",
    )
    (fake_pkg / "_github.py").write_text(
        "import json\n"
        "import subprocess\n"
        "import sys\n"
        "\n"
        "\n"
        "def fetch_issue_body(organization, repo, issue):\n"
        "    result = subprocess.run(\n"
        "        ['gh', 'api',\n"
        "         f'repos/{organization}/{repo}/issues/{issue}',\n"
        "         '--jq', '.body'],\n"
        "        capture_output=True, text=True, check=False,\n"
        "    )\n"
        "    if result.returncode != 0:\n"
        "        sys.exit(1)\n"
        "    return result.stdout\n"
        "\n"
        "\n"
        "def update_issue_body(organization, repo, issue, body):\n"
        "    payload = json.dumps({'body': body})\n"
        "    result = subprocess.run(\n"
        "        ['gh', 'api',\n"
        "         f'repos/{organization}/{repo}/issues/{issue}',\n"
        "         '-X', 'PATCH', '--input', '-'],\n"
        "        input=payload,\n"
        "        capture_output=True, text=True, check=False,\n"
        "    )\n"
        "    if result.returncode != 0:\n"
        "        sys.exit(1)\n",
        encoding="utf-8",
    )
    return str(fake_scripts)


def _install_fake_gh(tmp_path, issue_body=""):
    """Install a fake gh that handles POST, PATCH, and --jq requests."""
    fake_bin = tmp_path / "fake_bin"
    fake_bin.mkdir(exist_ok=True)
    gh_script = fake_bin / "gh"
    escaped_body = issue_body.replace("'", "'\\''")
    gh_script.write_text(
        '#!/bin/sh\n'
        'for arg in "$@"; do\n'
        '  if [ "$arg" = "POST" ]; then\n'
        '    echo \'{"number": 999}\'\n'
        '    exit 0\n'
        '  fi\n'
        'done\n'
        'for arg in "$@"; do\n'
        '  if [ "$arg" = ".body" ]; then\n'
        f'    printf \'%s\' \'{escaped_body}\'\n'
        '    exit 0\n'
        '  fi\n'
        'done\n'
        'exit 0\n',
        encoding="utf-8",
    )
    gh_script.chmod(gh_script.stat().st_mode | stat.S_IEXEC)
    return str(fake_bin)


def _base_env(tmp_path, fake_scripts_dir, issue_body=""):
    """Build subprocess env with fake classify_test before real scripts."""
    env = os.environ.copy()
    env["HOME"] = str(tmp_path)
    pypath = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = os.pathsep.join(
        [fake_scripts_dir, _SCRIPTS_DIR]
        + ([pypath] if pypath else []),
    )
    fake_bin = _install_fake_gh(tmp_path, issue_body=issue_body)
    env["PATH"] = fake_bin + os.pathsep + env.get("PATH", "")
    return env


def _invoke(*args, cwd=None, env=None):
    """Run classify_file in a child process."""
    run_env = (env or os.environ).copy()
    if "PYTHONPATH" not in run_env:
        pypath = run_env.get("PYTHONPATH", "")
        run_env["PYTHONPATH"] = (
            _SCRIPTS_DIR + os.pathsep + pypath
            if pypath else _SCRIPTS_DIR
        )
    return subprocess.run(
        [sys.executable, "-m", "classify_file", *args],
        capture_output=True,
        text=True,
        cwd=cwd,
        env=run_env,
        check=False,
    )


def _write_test_file(tmp_path, body):
    """Write test_input.cpp and return its path."""
    f = tmp_path / "test_input.cpp"
    f.write_text(body, encoding="utf-8")
    return f


def _all_flags(tmp_path):
    """Return the full set of required CLI flags."""
    return [
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", str(tmp_path / "lrm.txt"),
        "--issue", "1",
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
    ]


def _all_flags_create(tmp_path):
    """Return CLI flags with --create-issue instead of --issue."""
    return [
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", str(tmp_path / "lrm.txt"),
        "--create-issue",
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
    ]


def _run_batch(tmp_path, body, exit_code=0):
    """Write *body*, install fake classify_test, and invoke classify_file."""
    fake = _install_fake_classify_test(tmp_path, exit_code=exit_code)
    env = _base_env(tmp_path, fake)
    _write_test_file(tmp_path, body)
    return _invoke(
        *_all_flags(tmp_path),
        cwd=str(tmp_path), env=env,
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage(tmp_path):
    """Running with no arguments prints usage to stderr."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "usage:" in _invoke(cwd=str(tmp_path), env=env).stderr


def test_usage_shows_classify_file(tmp_path):
    """Usage line shows 'classify_file' as program name."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "classify_file" in _invoke(
        cwd=str(tmp_path), env=env,
    ).stderr


def test_missing_file_flag_reported(tmp_path):
    """Omitting --file reports the missing argument."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    assert "--file" in _invoke(
        "--output-dir", str(tmp_path),
        "--lrm", "lrm.txt",
        cwd=str(tmp_path), env=env,
    ).stderr


# ---- Input validation errors -----------------------------------------------


def test_nonexistent_file_reports_error(tmp_path):
    """Pointing --file at a missing path prints ERROR."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    flags = _all_flags(tmp_path)
    flags[flags.index("--file") + 1] = str(tmp_path / "missing.cpp")
    result = _invoke(*flags, cwd=str(tmp_path), env=env)
    assert "ERROR" in result.stdout


def test_file_without_tests_reports_error(tmp_path):
    """A file with no TEST blocks prints an error."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    _write_test_file(tmp_path, "#include <gtest/gtest.h>\n")
    result = _invoke(
        *_all_flags(tmp_path),
        cwd=str(tmp_path), env=env,
    )
    assert "No TEST blocks" in result.stdout


# ---- Successful batch run --------------------------------------------------


def test_batch_all_pass_exits_zero(tmp_path):
    """Exits 0 when all classify_test calls succeed."""
    result = _run_batch(
        tmp_path, "TEST(S, A) {\n}\nTEST(S, B) {\n}\n",
    )
    assert result.returncode == 0


def test_batch_all_pass_summary(tmp_path):
    """Summary shows all tests succeeded."""
    result = _run_batch(
        tmp_path, "TEST(S, A) {\n}\nTEST(S, B) {\n}\n",
    )
    assert "2/2 tests succeeded" in result.stdout


# ---- Failure batch run -----------------------------------------------------


def test_batch_failure_exits_one(tmp_path):
    """Exits 1 when classify_test fails."""
    result = _run_batch(
        tmp_path, "TEST(S, A) {\n}\n", exit_code=1,
    )
    assert result.returncode == 1


def test_batch_progress_output(tmp_path):
    """Progress lines show test index and name."""
    result = _run_batch(
        tmp_path,
        "TEST(S, Alpha) {\n}\nTEST(S, Beta) {\n}\n",
    )
    assert "Processing test 1/2: Alpha" in result.stdout


# ---- --create-issue --------------------------------------------------------


def test_create_issue_batch_exits_zero(tmp_path):
    """Exits 0 when --create-issue is used and all tests pass."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    _write_test_file(tmp_path, "TEST(S, A) {\n}\nTEST(S, B) {\n}\n")
    result = _invoke(
        *_all_flags_create(tmp_path),
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0


def test_create_issue_prints_created(tmp_path):
    """Stdout contains the created issue number."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    _write_test_file(tmp_path, "TEST(S, A) {\n}\n")
    result = _invoke(
        *_all_flags_create(tmp_path),
        cwd=str(tmp_path), env=env,
    )
    assert "Created issue #999" in result.stdout


def test_both_issue_flags_rejects(tmp_path):
    """Both --issue and --create-issue are rejected."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        "--issue", "1", "--create-issue",
        "--file", str(tmp_path / "f.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", "lrm.txt",
        "--organization", "org", "--repo", "repo",
        "--max-lines", "500",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode != 0


def test_neither_issue_flag_rejects(tmp_path):
    """Neither --issue nor --create-issue is rejected."""
    fake = _install_fake_classify_test(tmp_path)
    env = _base_env(tmp_path, fake)
    result = _invoke(
        "--file", str(tmp_path / "f.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", "lrm.txt",
        "--organization", "org", "--repo", "repo",
        "--max-lines", "500",
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode != 0


# ---- ensure_unchecked e2e --------------------------------------------------


def test_issue_unchecks_before_processing(tmp_path):
    """Unchecks checked boxes before processing when --issue is given."""
    fake = _install_fake_classify_test(tmp_path)
    issue_body = "- [x] Alpha\n- [ ] Beta\n"
    env = _base_env(tmp_path, fake, issue_body=issue_body)
    _write_test_file(
        tmp_path, "TEST(S, Alpha) {\n}\nTEST(S, Beta) {\n}\n",
    )
    result = _invoke(
        *_all_flags(tmp_path),
        cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0
