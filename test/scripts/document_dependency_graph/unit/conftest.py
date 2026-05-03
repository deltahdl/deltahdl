"""Shared fixtures for document_dependency_graph unit tests."""

from typing import Any
from unittest.mock import MagicMock, patch

import pytest

import document_dependency_graph
from document_dependency_graph.commit import commit_output


_DEFAULT_TOC: dict[str, tuple[int, int]] = {"4.4": (10, 20)}
_DEFAULT_RECORD: dict[str, Any] = {
    "dependencies": [],
    "proofs": {},
    "prerequisites": {},
}


@pytest.fixture()
def run_main(make_lrm, make_output):
    """Patch the walk hooks, run main(), and return the mock pair.

    The mocks (load_toc, build_subclause_record) are returned so each
    test can assert on call counts/args without re-stating the boiler
    plate of patching, building argv, and invoking main().
    """

    def _run(*, toc=None, record=None, extra_argv=None):
        toc_payload = _DEFAULT_TOC if toc is None else toc
        record_payload = _DEFAULT_RECORD if record is None else record
        argv = [
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ]
        if extra_argv:
            argv.extend(extra_argv)
        toc_patch = patch(
            "document_dependency_graph.load_toc",
            return_value=toc_payload,
        )
        record_patch = patch(
            "document_dependency_graph.build_subclause_record",
            return_value=record_payload,
        )
        commit_patch = patch(
            "document_dependency_graph.commit_output",
        )
        with toc_patch as mock_toc, record_patch as mock_record, \
                commit_patch as mock_commit:
            document_dependency_graph.main(argv)
        return mock_toc, mock_record, mock_commit

    return _run


def _completed(returncode=0, stdout=""):
    """Build a stubbed CompletedProcess for subprocess.run."""
    proc = MagicMock()
    proc.returncode = returncode
    proc.stdout = stdout
    proc.stderr = ""
    return proc


@pytest.fixture()
def run_commit(tmp_path):
    """Run commit_output(out) with a stubbed git; return (cmds, raised).

    ``cmds`` is the list of joined git commands the stub observed;
    ``raised`` is the RuntimeError if commit_output raised, else None.
    Each keyword toggles one branch of the git stub: dirty tree,
    empty staged diff, non-zero exit for add/commit/push.
    """

    def _make(
        *, dirty=False, staged_diff=True,
        git_add_rc=0, git_commit_rc=0, git_push_rc=0,
    ):
        out = tmp_path / "graph.json"
        out.write_text("{}")

        def _run(cmd, **_kwargs):
            joined = " ".join(cmd)
            if "git status --porcelain --untracked-files=no" in joined:
                return _completed(stdout="?? a\n" if dirty else "")
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
        with patch("document_dependency_graph.commit.subprocess.run", runner):
            try:
                commit_output(out)
            except RuntimeError as exc:
                raised = exc
        cmds = [" ".join(c.args[0]) for c in runner.call_args_list]
        return cmds, raised, out

    return _make
