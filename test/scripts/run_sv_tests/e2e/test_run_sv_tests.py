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


def _make_sv_tree(tmp_path: Path, metadata: str = "") -> Path:
    """Create a minimal sv-test tree with chapter dirs and .sv files.

    ``metadata`` is written above each module as an sv-tests block comment, so
    a caller can give the files the keys the script reads out of the corpus.
    """
    test_dir = tmp_path / "sv-tests"
    ch5 = test_dir / "chapter-5"
    ch5.mkdir(parents=True)
    (ch5 / "alpha.sv").write_text(f"{metadata}module alpha; endmodule\n")
    (ch5 / "beta.sv").write_text(f"{metadata}module beta; endmodule\n")
    return test_dir


def _run_sv_tests(
    tmp_path: Path,
    exit_code: int = 0,
    extra_args: list[str] | None = None,
    stderr: str = "",
    metadata: str = "",
) -> subprocess.CompletedProcess[str]:
    """Run run_sv_tests.py in a subprocess with patched BINARY and TEST_DIR.

    Returns the CompletedProcess.
    """
    binary = _make_stub_binary(tmp_path, exit_code=exit_code, stderr=stderr)
    test_dir = _make_sv_tree(tmp_path, metadata=metadata)

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
        env={**os.environ, "NO_COLOR": "1"},
    )


def test_all_pass_exit_zero_and_pass_in_output(tmp_path: Path) -> None:
    """With exit-0 stub, script exits 0 and stdout contains PASS."""
    result = _run_sv_tests(tmp_path, exit_code=0)
    assert (
        result.returncode == 0
        and "PASS" in result.stdout
        and "summary" in result.stdout
    )


def test_all_fail_exit_one_and_fail_in_output(tmp_path: Path) -> None:
    """With exit-1 stub, script exits 1 and stdout contains FAIL."""
    result = _run_sv_tests(tmp_path, exit_code=1)
    assert result.returncode == 1 and "FAIL" in result.stdout


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
    the ``(§7.3)`` form ``DiagEngine::Emit`` at ``src/common/diagnostic.cpp:47``
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
    assert "FAIL" in result.stdout and "exited -11" in result.stdout


def test_junit_xml_exit_code(tmp_path: Path) -> None:
    """With --junit-xml, the script exits 0 when all tests pass."""
    xml_path = str(tmp_path / "report.xml")
    result = _run_sv_tests(
        tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path]
    )
    assert result.returncode == 0 and Path(xml_path).exists()


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
