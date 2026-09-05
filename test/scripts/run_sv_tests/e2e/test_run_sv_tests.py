"""End-to-end tests for run_sv_tests module."""

import os
import stat
import subprocess
import sys
import textwrap
from pathlib import Path
from xml.etree import ElementTree as ET

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"


def _make_stub_binary(
    tmp_path: Path, exit_code: int = 0, stderr: str = "",
) -> Path:
    """Create a stub deltahdl binary that writes ``stderr`` and exits with the code.

    A negative ``exit_code`` makes the stub die on the signal of that number
    rather than exit, which is how a simulator that crashes leaves the process.
    The sign carries it because that is how ``subprocess`` reports it back: a
    process killed by signal 11 has a return code of -11.
    """
    binary = tmp_path / "deltahdl"
    lines = ["#!/usr/bin/env bash"]
    if stderr:
        quoted = stderr.replace("'", "'\\''")
        lines.append(f"printf '%s' '{quoted}' >&2")
    if exit_code < 0:
        lines.append(f"kill -{-exit_code} $$")
    else:
        lines.append(f"exit {exit_code}")
    binary.write_text("\n".join(lines) + "\n")
    binary.chmod(binary.stat().st_mode | stat.S_IEXEC)
    return binary


def _sv_tree_path(tmp_path: Path) -> Path:
    """Return the directory ``_make_sv_tree`` writes the corpus into."""
    return tmp_path / "sv-tests"


def _commit_sv_tree(test_dir: Path) -> None:
    """Make ``test_dir`` a git repository holding everything written in it.

    The corpus the script reads in CI is a clone, so it has a commit the run
    can be quoted against. The identity is given on the command line because a
    runner has none configured, and writing one into the configuration of a
    machine that does would change that machine outside the test.
    """
    subprocess.run(
        ["git", "-c", "init.defaultBranch=main", "init", str(test_dir)],
        capture_output=True, text=True, timeout=30, check=True,
    )
    subprocess.run(
        ["git", "-C", str(test_dir), "add", "."],
        capture_output=True, text=True, timeout=30, check=True,
    )
    subprocess.run(
        [
            "git",
            "-c", "user.email=tests@deltahdl.invalid",
            "-c", "user.name=deltahdl tests",
            "-c", "commit.gpgsign=false",
            "-C", str(test_dir),
            "commit", "-m", "sv-tests corpus",
        ],
        capture_output=True, text=True, timeout=30, check=True,
    )


def _head_commit(tmp_path: Path) -> str:
    """Return the commit HEAD names in the corpus tree under ``tmp_path``."""
    result = subprocess.run(
        ["git", "-C", str(_sv_tree_path(tmp_path)), "rev-parse", "HEAD"],
        capture_output=True, text=True, timeout=30, check=True,
    )
    return result.stdout.strip()


def _make_sv_tree(
    tmp_path: Path, metadata: str = "", git_init: bool = False,
) -> Path:
    """Create a minimal sv-test tree with chapter dirs and .sv files.

    ``metadata`` is written above each module as an sv-tests block comment, so
    a caller can give the files the keys the script reads out of the corpus.
    ``git_init`` commits the tree into a repository of its own, which is what
    gives the corpus a revision to be named by; without it the tree is a plain
    directory, which is the other shape the script has to report on.
    """
    test_dir = _sv_tree_path(tmp_path)
    ch5 = test_dir / "chapter-5"
    ch5.mkdir(parents=True)
    (ch5 / "alpha.sv").write_text(f"{metadata}module alpha; endmodule\n")
    (ch5 / "beta.sv").write_text(f"{metadata}module beta; endmodule\n")
    if git_init:
        _commit_sv_tree(test_dir)
    return test_dir


def _run_over_tree(
    test_dir: Path,
    binary: Path,
    extra_args: list[str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run run_sv_tests.py over ``test_dir`` with ``binary`` as the tool.

    ``GIT_CEILING_DIRECTORIES`` stops git climbing above the directory holding
    the corpus, so a corpus written without a repository of its own reports no
    revision even when the temporary directory sits inside somebody's checkout.
    ``GIT_DIR`` and ``GIT_WORK_TREE`` are dropped because either one names a
    repository outright and is read before the ceiling is consulted.

    Returns the CompletedProcess.
    """
    env = {
        k: v
        for k, v in os.environ.items()
        if k not in ("GIT_DIR", "GIT_WORK_TREE")
    }
    args_str = ""
    if extra_args:
        args_str = ", ".join(repr(a) for a in extra_args)
        args_str = ", " + args_str

    code = textwrap.dedent(f"""\
        import sys
        sys.path.insert(0, {str(REPO_ROOT)!r})
        sys.path.insert(0, {str(SCRIPTS_DIR)!r})

        import run_sv_tests
        from lib.python import run_tests_common
        from pathlib import Path

        run_tests_common.BINARY = Path({str(binary)!r})
        run_sv_tests.BINARY = run_tests_common.BINARY
        run_sv_tests.TEST_DIR = Path({str(test_dir)!r})

        sys.argv = ["run_sv_tests.py"{args_str}]
        run_sv_tests.main()
    """)

    return subprocess.run(
        [sys.executable, "-c", code],
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
        env={
            **env,
            "NO_COLOR": "1",
            "GIT_CEILING_DIRECTORIES": str(test_dir.parent),
        },
    )


def _run_sv_tests(
    tmp_path: Path,
    exit_code: int = 0,
    extra_args: list[str] | None = None,
    stderr: str = "",
    metadata: str = "",
) -> subprocess.CompletedProcess[str]:
    """Run run_sv_tests.py in a subprocess with patched BINARY and TEST_DIR.

    The corpus is a plain directory with no repository around it. A test that
    needs one commits the tree with ``_make_sv_tree(git_init=True)`` and runs
    it through ``_run_over_tree``.

    Returns the CompletedProcess.
    """
    binary = _make_stub_binary(tmp_path, exit_code=exit_code, stderr=stderr)
    test_dir = _make_sv_tree(tmp_path, metadata=metadata)
    return _run_over_tree(test_dir, binary, extra_args)


def test_all_pass_exit_zero(tmp_path: Path) -> None:
    """With exit-0 stub, the script exits 0."""
    assert _run_sv_tests(tmp_path, exit_code=0).returncode == 0


def test_all_pass_prints_pass(tmp_path: Path) -> None:
    """With exit-0 stub, the script reports the file as a pass."""
    assert "PASS" in _run_sv_tests(tmp_path, exit_code=0).stdout


def test_all_pass_prints_a_summary(tmp_path: Path) -> None:
    """With exit-0 stub, the script closes the run with a summary."""
    assert "summary" in _run_sv_tests(tmp_path, exit_code=0).stdout


def test_all_fail_exit_one(tmp_path: Path) -> None:
    """With exit-1 stub, the script exits 1."""
    assert _run_sv_tests(tmp_path, exit_code=1).returncode == 1


def test_all_fail_prints_fail(tmp_path: Path) -> None:
    """With exit-1 stub, the script reports the file as a failure."""
    assert "FAIL" in _run_sv_tests(tmp_path, exit_code=1).stdout


def test_expected_rejection_prints_the_stub_diagnostic(tmp_path: Path) -> None:
    """A file marked to be rejected is reported with the rejection it drew.

    The file passes because the tool refused it, so the refusal is the only
    thing in the run that says which refusal it was.
    """
    result = _run_sv_tests(
        tmp_path,
        exit_code=1,
        stderr="alpha.sv:1:1: error: redeclaration of 'v'",
        metadata="/*\n:should_fail_because: Variable redeclaration\n*/\n",
    )
    assert "alpha.sv:1:1: error: redeclaration of 'v'" in result.stdout


def test_rejection_naming_a_different_clause_reports_fail(
    tmp_path: Path,
) -> None:
    """A file rejected under a clause it is not tagged with is reported FAIL.

    The corpus tags the file ``6.19``, and the stub rejects it naming §7.3, in
    the ``(§7.3)`` form ``DiagEngine::Emit`` in ``src/common/diagnostic.cpp``
    appends to a message. A rejection enforcing some other rule of the standard
    is not the file exercising the clause it was written for, so scoring it a
    pass would report the corpus as covering §6.19 when nothing did.
    """
    result = _run_sv_tests(
        tmp_path,
        exit_code=1,
        stderr="alpha.sv:1:1: error: 'v' is not a class type (§7.3)",
        metadata=(
            "/*\n"
            ":should_fail_because: An enumerated name assigned x or z\n"
            ":tags: 6.19\n"
            "*/\n"
        ),
    )
    assert "FAIL" in result.stdout


def test_crashing_stub_reports_fail_for_an_expected_rejection(
    tmp_path: Path,
) -> None:
    """A tool that dies on a file has not rejected the file it died on.

    The stub is killed by a real signal rather than made to report a code, so
    this is the tier that shows what the runner does with the process state a
    crashed simulator actually leaves.
    """
    result = _run_sv_tests(
        tmp_path,
        exit_code=-11,
        metadata="/*\n:should_fail_because: Variable redeclaration\n*/\n",
    )
    missing = [t for t in ("FAIL", "exited -11") if t not in result.stdout]
    assert not missing


def test_junit_xml_exit_code(tmp_path: Path) -> None:
    """With --junit-xml, the script exits 0 when all tests pass."""
    xml_path = str(tmp_path / "report.xml")
    result = _run_sv_tests(
        tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path]
    )
    assert result.returncode == 0


def test_junit_xml_writes_the_report(tmp_path: Path) -> None:
    """With --junit-xml, the script writes the report at the path given."""
    xml_path = str(tmp_path / "report.xml")
    _run_sv_tests(tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path])
    assert Path(xml_path).exists()


def test_junit_xml_structure(tmp_path: Path) -> None:
    """With --junit-xml, the script writes a parseable XML file."""
    xml_path = str(tmp_path / "report.xml")
    _run_sv_tests(
        tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path]
    )

    tree = ET.parse(xml_path)
    root = tree.getroot()
    assert (
        root.tag, root.attrib["tests"], root.attrib["failures"]
    ) == ("testsuite", "2", "0")


def test_summary_names_the_corpus_commit(tmp_path: Path) -> None:
    """Run the script over a corpus that is a repository and read HEAD back.

    A count of how many corpus files passed cannot be compared with a later
    count unless the report says which corpus was counted, and the corpus is a
    clone of an upstream repository that moves between runs. This fails if the
    summary omits the commit the tree the files came from is checked out at,
    or names some other checkout's commit.
    """
    binary = _make_stub_binary(tmp_path, exit_code=0)
    test_dir = _make_sv_tree(tmp_path, git_init=True)
    result = _run_over_tree(test_dir, binary)
    assert _head_commit(tmp_path) in result.stdout


def test_summary_reports_an_unknown_corpus_outside_a_repository(
    tmp_path: Path,
) -> None:
    """Run the script over a plain corpus directory and read "unknown" back.

    A corpus with no repository around it is what an unpacked tree gives, and
    the run is scored on the files rather than on where they came from, so the
    missing revision is a label the report fills in. This fails if a tree with
    no commit to name stops the run or drops the line instead.
    """
    result = _run_sv_tests(tmp_path, exit_code=0)
    assert "sv-tests corpus: unknown" in result.stdout
