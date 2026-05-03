"""End-to-end tests for the classify_files CLI."""

import subprocess
from pathlib import Path

import pytest

from lib.python.test_utils import (
    build_base_env,
    e2e_base_flags,
    install_fake_script,
    invoke_module,
)

_SCRIPTS_DIR = str(
    Path(__file__).resolve().parents[4] / "scripts",
)


# ---- Helpers ---------------------------------------------------------------


def _install_fakes(tmp_path: Path, exit_code: int = 0) -> str:
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
        "import re\n"
        "\n"
        "def fetch_issue_body(_org, _repo, _issue):\n"
        "    return '| a.cpp | Unreviewed | |\\n| b.cpp | Unreviewed | |\\n'\n"
        "\n"
        "def remove_test_row(body, name):\n"
        "    pattern = re.compile(\n"
        "        r'^\\| ' + re.escape(name)"
        " + r' \\|[^|]*\\|[^|]*\\|\\n?', re.MULTILINE,\n"
        "    )\n"
        "    return pattern.sub('', body)\n"
        "\n"
        "def update_issue_body(_org, _repo, _issue, _body):\n"
        "    pass\n",
        encoding="utf-8",
    )
    return str(fake_scripts)


def _install_fake_gh(
        tmp_path: Path, titles: dict[str, str] | None = None) -> str:
    """Install a fake gh that succeeds for all requests.

    *titles* maps issue number strings to title strings for
    ``--jq .title`` requests.
    """
    title_cases = ""
    for number, title in (titles or {}).items():
        escaped = title.replace("'", "'\\''")
        title_cases += (
            f'  if echo "$@" | grep -q "issues/{number}"; then\n'
            f"    printf '%s' '{escaped}'\n"
            f'    exit 0\n'
            f'  fi\n'
        )
    return install_fake_script(
        tmp_path, "gh",
        '#!/bin/sh\n'
        'for arg in "$@"; do\n'
        '  if [ "$arg" = ".title" ]; then\n'
        + title_cases +
        '    exit 1\n'
        '  fi\n'
        'done\n'
        'echo \'{"body": "- [ ] a.cpp\\n- [ ] b.cpp"}\'\n'
        'exit 0\n',
    )


def _base_env(
        tmp_path: Path, fake_scripts_dir: str,
        titles: dict[str, str] | None = None) -> dict[str, str]:
    """Build subprocess env with fake classify_file before real scripts."""
    fake_bin = _install_fake_gh(tmp_path, titles=titles)
    return build_base_env(tmp_path, fake_scripts_dir, fake_bin)


def _invoke(
        *args: str, cwd: str | None = None,
        env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run classify_files in a child process."""
    return invoke_module("classify_files", *args, cwd=cwd, env=env)


def _all_flags(tmp_path: Path) -> list[str]:
    """Return the full set of required CLI flags."""
    return [
        "--files", "a.cpp,b.cpp",
        "--issue", "1",
        *e2e_base_flags(tmp_path),
    ]


def _all_flags_sub_issues(tmp_path: Path) -> list[str]:
    """Return CLI flags with --sub-issues instead of --files."""
    return [
        "--sub-issues", "1,2",
        "--issue", "1",
        *e2e_base_flags(tmp_path),
    ]


def _fresh_env(tmp_path: Path, exit_code: int = 0) -> dict[str, str]:
    """Install fakes and return a subprocess env."""
    return _base_env(tmp_path, _install_fakes(tmp_path, exit_code=exit_code))


def _run_batch(
        tmp_path: Path,
        exit_code: int = 0) -> subprocess.CompletedProcess[str]:
    """Install fake classify_file and invoke classify_files."""
    return _invoke(
        *_all_flags(tmp_path),
        cwd=str(tmp_path), env=_fresh_env(tmp_path, exit_code),
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage(tmp_path: Path) -> None:
    """Running with no arguments prints usage to stderr."""
    assert "usage:" in _invoke(
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


def test_usage_shows_classify_files(tmp_path: Path) -> None:
    """Usage line shows classify_files as program name."""
    assert "classify_files" in _invoke(
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


def test_missing_files_flag_reported(tmp_path: Path) -> None:
    """Omitting --files reports the missing argument."""
    assert "--files" in _invoke(
        "--issue", "1",
        *e2e_base_flags(tmp_path),
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    ).stderr


# ---- Successful batch run --------------------------------------------------


def test_batch_all_pass_exits_zero(tmp_path: Path) -> None:
    """Exits 0 when all classify_file calls succeed."""
    assert _run_batch(tmp_path).returncode == 0


# ---- Failure batch run -----------------------------------------------------


def test_batch_failure_exits_one(tmp_path: Path) -> None:
    """Exits 1 when classify_file fails."""
    assert _run_batch(tmp_path, exit_code=1).returncode == 1


# ---- Progress output -------------------------------------------------------


def test_batch_progress_output(tmp_path: Path) -> None:
    """Progress lines show file index and name."""
    result = _run_batch(tmp_path)
    assert "Processing file 1/2: a.cpp" in result.stdout


# ---- --sub-issues ---------------------------------------------------------


def test_sub_issues_batch_exits_zero(tmp_path: Path) -> None:
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


@pytest.mark.parametrize("extra", [
    ["--dry-run"],
    ["--no-commit"],
], ids=["dry-run", "no-commit"])
def test_optional_flag_accepted(tmp_path: Path, extra: list[str]) -> None:
    """Optional flags are accepted and exit 0."""
    result = _invoke(
        *_all_flags(tmp_path), *extra,
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    )
    assert result.returncode == 0


def test_both_flags_rejects(tmp_path: Path) -> None:
    """--files and --sub-issues together are rejected."""
    result = _invoke(
        "--files", "a.cpp",
        "--sub-issues", "1",
        "--issue", "1",
        *e2e_base_flags(tmp_path),
        cwd=str(tmp_path), env=_fresh_env(tmp_path),
    )
    assert result.returncode != 0
