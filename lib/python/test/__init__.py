"""Shared test utilities."""

import os
import subprocess
import sys
from pathlib import Path

_SCRIPTS_DIR = str(
    Path(__file__).resolve().parents[3] / "scripts",
)


def build_base_env(tmp_path, fake_scripts_dir, fake_bin):
    """Build a subprocess env with *fake_scripts_dir* before real scripts."""
    env = os.environ.copy()
    env["HOME"] = str(tmp_path)
    pypath = env.get("PYTHONPATH", "")
    env["PYTHONPATH"] = os.pathsep.join(
        [fake_scripts_dir, _SCRIPTS_DIR]
        + ([pypath] if pypath else []),
    )
    env["PATH"] = fake_bin + os.pathsep + env.get("PATH", "")
    return env


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
