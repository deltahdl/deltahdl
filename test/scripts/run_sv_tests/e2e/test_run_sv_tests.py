"""End-to-end tests for run_sv_tests module."""

import os
import stat
import subprocess
import sys
import textwrap
from pathlib import Path
from xml.etree import ElementTree as ET

from lib import test_common

REPO_ROOT = test_common.REPO_ROOT
SCRIPTS_DIR = REPO_ROOT / "scripts"


def _make_stub_binary(tmp_path, exit_code=0, stderr=""):
    """Create a stub deltahdl binary that exits with the given code."""
    binary = tmp_path / "deltahdl"
    lines = ["#!/usr/bin/env bash"]
    if stderr:
        quoted = stderr.replace("'", "'\\''")
        lines.append(f"printf '%s' '{quoted}' >&2")
    lines.append(f"exit {exit_code}")
    binary.write_text("\n".join(lines) + "\n")
    binary.chmod(binary.stat().st_mode | stat.S_IEXEC)
    return binary


def _make_sv_tree(tmp_path):
    """Create a minimal sv-test tree with chapter dirs and .sv files."""
    test_dir = tmp_path / "sv-tests"
    ch5 = test_dir / "chapter-5"
    ch5.mkdir(parents=True)
    (ch5 / "alpha.sv").write_text("module alpha; endmodule\n")
    (ch5 / "beta.sv").write_text("module beta; endmodule\n")
    return test_dir


def _run_sv_tests(tmp_path, exit_code=0, extra_args=None):
    """Run run_sv_tests.py in a subprocess with patched BINARY and TEST_DIR.

    Returns the CompletedProcess.
    """
    binary = _make_stub_binary(tmp_path, exit_code=exit_code)
    test_dir = _make_sv_tree(tmp_path)

    args_str = ""
    if extra_args:
        args_str = ", ".join(repr(a) for a in extra_args)
        args_str = ", " + args_str

    code = textwrap.dedent(f"""\
        import sys
        sys.path.insert(0, {str(REPO_ROOT)!r})
        sys.path.insert(0, {str(SCRIPTS_DIR)!r})

        import run_sv_tests
        from lib import test_common
        from pathlib import Path

        test_common.BINARY = Path({str(binary)!r})
        run_sv_tests.BINARY = test_common.BINARY
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


def test_all_pass_exit_zero_and_pass_in_output(tmp_path):
    """With exit-0 stub, script exits 0 and stdout contains PASS."""
    result = _run_sv_tests(tmp_path, exit_code=0)
    assert (
        result.returncode == 0
        and "PASS" in result.stdout
        and "summary" in result.stdout
    )


def test_all_fail_exit_one_and_fail_in_output(tmp_path):
    """With exit-1 stub, script exits 1 and stdout contains FAIL."""
    result = _run_sv_tests(tmp_path, exit_code=1)
    assert result.returncode == 1 and "FAIL" in result.stdout


def test_junit_xml_exit_code(tmp_path):
    """With --junit-xml, the script exits 0 when all tests pass."""
    xml_path = str(tmp_path / "report.xml")
    result = _run_sv_tests(
        tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path]
    )
    assert result.returncode == 0 and Path(xml_path).exists()


def test_junit_xml_structure(tmp_path):
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
