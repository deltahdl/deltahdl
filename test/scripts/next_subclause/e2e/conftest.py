"""Shared fixtures for next_subclause e2e tests."""

import json
import os
import stat
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[4]


@pytest.fixture()
def run_cli(tmp_path: Path) -> Callable[..., subprocess.CompletedProcess[str]]:
    """Return a factory running the CLI with a stub ``gh`` answering *issues*.

    The stub is put first on the path, so the command under test resolves
    it the way it resolves the real one. Nothing here reaches the network
    or depends on what the repository's issues happen to be today.
    """
    def _run(
        graph: Path, issues: list[dict[str, Any]],
    ) -> subprocess.CompletedProcess[str]:
        bin_dir = tmp_path / "bin"
        bin_dir.mkdir(exist_ok=True)
        gh = bin_dir / "gh"
        gh.write_text(
            "#!/usr/bin/env bash\n"
            f"cat <<'PAYLOAD'\n{json.dumps(issues)}\nPAYLOAD\n",
        )
        gh.chmod(gh.stat().st_mode | stat.S_IEXEC)
        env = dict(os.environ)
        env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
        env["PYTHONPATH"] = f"{REPO_ROOT}{os.pathsep}{REPO_ROOT / 'scripts'}"
        return subprocess.run(
            [sys.executable, "-m", "next_subclause", "--graph", str(graph)],
            capture_output=True, check=False, env=env, text=True,
        )

    return _run
