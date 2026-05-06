"""Shared fixtures for generate_lrm_subclause_dependencies unit tests."""

from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

import generate_lrm_subclause_dependencies
from generate_lrm_subclause_dependencies.commit import (
    assert_clean_tree,
    commit_output,
)


_DEFAULT_TOC: dict[str, tuple[int, int]] = {"4.4": (10, 20)}
_DEFAULT_RECORD: dict[str, Any] = {"dependencies": []}


@pytest.fixture()
def run_main(
    make_lrm: Path, make_output: Path,
) -> Callable[..., tuple[MagicMock, MagicMock, MagicMock]]:
    """Patch the walk hooks, run main(), and return the mock pair.

    The mocks (load_toc, build_subclause_record, commit_output) are
    returned so each test can assert on call counts/args without
    re-stating the boilerplate of patching, building argv, and
    invoking main(). assert_clean_tree is stubbed silently because
    --commit-using tests should not actually shell out to git status.
    """

    def _run(
        *,
        toc: dict[str, tuple[int, int]] | None = None,
        record: dict[str, Any] | None = None,
        extra_argv: Sequence[str] | None = None,
    ) -> tuple[MagicMock, MagicMock, MagicMock]:
        toc_payload = _DEFAULT_TOC if toc is None else toc
        record_payload = _DEFAULT_RECORD if record is None else record
        argv = [
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ]
        if extra_argv:
            argv.extend(extra_argv)
        toc_patch = patch(
            "generate_lrm_subclause_dependencies.load_toc",
            return_value=toc_payload,
        )
        record_patch = patch(
            "generate_lrm_subclause_dependencies.build_subclause_record",
            return_value=record_payload,
        )
        commit_patch = patch(
            "generate_lrm_subclause_dependencies.commit_output",
        )
        clean_patch = patch(
            "generate_lrm_subclause_dependencies.assert_clean_tree",
        )
        with toc_patch as mock_toc, record_patch as mock_record, \
                commit_patch as mock_commit, clean_patch as _clean:
            del _clean
            generate_lrm_subclause_dependencies.main(argv)
        return mock_toc, mock_record, mock_commit

    return _run


def _completed(returncode: int = 0, stdout: str = "") -> MagicMock:
    """Build a stubbed CompletedProcess for subprocess.run."""
    proc = MagicMock()
    proc.returncode = returncode
    proc.stdout = stdout
    proc.stderr = ""
    return proc


@pytest.fixture()
def run_commit(
    tmp_path: Path,
) -> Callable[..., tuple[list[str], RuntimeError | None, Path]]:
    """Run commit_output(out, message=...) with a stubbed git.

    Returns (cmds, raised, out): the joined git commands the stub
    observed, the RuntimeError if commit_output raised (else None),
    and the output Path. Keyword args toggle the stub's per-command
    behavior so each test can drive one branch.
    """

    def _make(
        *,
        message: str = "test-message",
        staged_diff: bool = True,
        git_add_rc: int = 0,
        git_commit_rc: int = 0,
        git_push_rc: int = 0,
    ) -> tuple[list[str], RuntimeError | None, Path]:
        out = tmp_path / "graph.json"
        out.write_text("{}")

        def _run(cmd: list[str], **_kwargs: Any) -> MagicMock:
            joined = " ".join(cmd)
            if "git diff --cached --quiet" in joined:
                return _completed(returncode=1 if staged_diff else 0)
            if "git add" in joined:
                return _completed(returncode=git_add_rc)
            if "git commit" in joined:
                return _completed(returncode=git_commit_rc)
            if "git push" in joined:
                return _completed(returncode=git_push_rc)
            return _completed()

        runner = MagicMock(side_effect=_run)
        raised: RuntimeError | None = None
        with patch("generate_lrm_subclause_dependencies.commit.subprocess.run", runner):
            try:
                commit_output(out, message=message)
            except RuntimeError as exc:
                raised = exc
        cmds = [" ".join(c.args[0]) for c in runner.call_args_list]
        return cmds, raised, out

    return _make


@pytest.fixture()
def run_assert_clean_tree() -> Callable[..., RuntimeError | None]:
    """Run assert_clean_tree() with a stubbed git status; return raised.

    ``dirty=True`` makes the stubbed `git status --porcelain` return
    one modified line so the assertion raises; ``dirty=False`` returns
    empty stdout so it passes.
    """

    def _make(*, dirty: bool = False) -> RuntimeError | None:
        def _run(cmd: list[str], **_kwargs: Any) -> MagicMock:
            joined = " ".join(cmd)
            if "git status --porcelain --untracked-files=no" in joined:
                return _completed(stdout=" M unrelated\n" if dirty else "")
            return _completed()

        runner = MagicMock(side_effect=_run)
        raised: RuntimeError | None = None
        with patch("generate_lrm_subclause_dependencies.commit.subprocess.run", runner):
            try:
                assert_clean_tree()
            except RuntimeError as exc:
                raised = exc
        return raised

    return _make
