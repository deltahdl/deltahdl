"""Shared test utilities."""

import importlib.util
import os
import stat
import subprocess
import sys
from pathlib import Path
from types import ModuleType

_REPO_ROOT = str(Path(__file__).resolve().parents[3])
_SCRIPTS_DIR = str(Path(_REPO_ROOT) / "scripts")


def load_module_from_path(module_name: str, path: Path) -> ModuleType:
    """Load a Python module from a file path."""
    spec = importlib.util.spec_from_file_location(module_name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def build_base_env(tmp_path, fake_scripts_dir, fake_bin):
    """Build a subprocess env with *fake_scripts_dir* before real scripts."""
    env = os.environ.copy()
    env["HOME"] = str(tmp_path)
    pypath = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = os.pathsep.join(
        [fake_scripts_dir, _SCRIPTS_DIR, _REPO_ROOT]
        + ([pypath] if pypath else []),
    )
    env["PATH"] = fake_bin + os.pathsep + env.get("PATH", "")
    return env


def install_fake_script(tmp_path, name, content):
    """Write an executable shell script into ``tmp_path/fake_bin/``.

    Returns the ``fake_bin`` directory path as a string (suitable for
    prepending to ``$PATH``).
    """
    fake_bin = tmp_path / "fake_bin"
    fake_bin.mkdir(exist_ok=True)
    script = fake_bin / name
    script.write_text(content, encoding="utf-8")
    script.chmod(script.stat().st_mode | stat.S_IEXEC)
    return str(fake_bin)


def install_fake_gh(
    tmp_path, issue_body="", issue_title="", handle_post=False,
):
    """Install a fake ``gh`` CLI that handles common API patterns.

    Handles ``--jq .body`` (returns *issue_body*),
    ``--jq .title`` (returns *issue_title*),
    PATCH (no-op success),
    and optionally POST (returns ``{"number": 999}``).
    """
    escaped_body = issue_body.replace("'", "'\\''")
    escaped_title = issue_title.replace("'", "'\\''")
    lines = ['#!/bin/sh\n']
    if handle_post:
        lines.append(
            'for arg in "$@"; do\n'
            '  if [ "$arg" = "POST" ]; then\n'
            '    echo \'{"number": 999}\'\n'
            '    exit 0\n'
            '  fi\n'
            'done\n',
        )
    lines.append(
        'for arg in "$@"; do\n'
        '  if [ "$arg" = ".body" ]; then\n'
        f'    printf \'%s\' \'{escaped_body}\'\n'
        '    exit 0\n'
        '  fi\n'
        '  if [ "$arg" = ".title" ]; then\n'
        f'    printf \'%s\' \'{escaped_title}\'\n'
        '    exit 0\n'
        '  fi\n'
        'done\n'
        'exit 0\n',
    )
    return install_fake_script(tmp_path, "gh", "".join(lines))


def install_fake_package(tmp_path, name, exit_code=0):
    """Install a fake Python package that exits with *exit_code*.

    Returns the directory to prepend to PYTHONPATH so the fake
    shadows the real package.
    """
    fake_scripts = tmp_path / "fake_scripts"
    fake_pkg = fake_scripts / name
    fake_pkg.mkdir(parents=True)
    (fake_pkg / "__init__.py").write_text("", encoding="utf-8")
    (fake_pkg / "__main__.py").write_text(
        f"import sys; sys.exit({exit_code})\n",
        encoding="utf-8",
    )
    return str(fake_scripts)


def e2e_base_flags(tmp_path):
    """Return the shared CLI flags common to all classify e2e tests."""
    return [
        "--output-dir", str(tmp_path),
        "--lrm", str(tmp_path / "lrm.txt"),
        "--organization", "org",
        "--repo", "repo",
        "--max-lines", "500",
    ]


def invoke_module(module_name, *args, cwd=None, env=None):
    """Run *module_name* in a child process via ``python -m``."""
    run_env = (env or os.environ).copy()
    if "PYTHONPATH" not in run_env:
        pypath = run_env.get("PYTHONPATH", "")
        run_env["PYTHONPATH"] = (
            _SCRIPTS_DIR + os.pathsep + pypath
            if pypath else _SCRIPTS_DIR
        )
    return subprocess.run(
        [sys.executable, "-m", module_name, *args],
        capture_output=True,
        text=True,
        cwd=cwd,
        env=run_env,
        check=False,
    )
