"""Shared test utilities."""

import os
import stat
import subprocess
import sys
from pathlib import Path

_REPO_ROOT = str(Path(__file__).resolve().parents[3])
_SCRIPTS_DIR = str(Path(_REPO_ROOT) / "scripts")


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
