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
    return tmp_path / "sv-tests"


def _commit_sv_tree(test_dir: Path) -> None:
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
            "commit", "-m", "sv-tests suite",
        ],
        capture_output=True, text=True, timeout=30, check=True,
    )


def _head_commit(tmp_path: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(_sv_tree_path(tmp_path)), "rev-parse", "HEAD"],
        capture_output=True, text=True, timeout=30, check=True,
    )
    return result.stdout.strip()


def _make_sv_tree(
    tmp_path: Path, metadata: str = "", git_init: bool = False,
) -> Path:
    test_dir = _sv_tree_path(tmp_path)
    ch5 = test_dir / "chapter-5"
    ch5.mkdir(parents=True)
    conf = test_dir.parent / "conf" / "runners"
    conf.mkdir(parents=True)
    (conf / "libs.json").write_text("{}\n")
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
    binary = _make_stub_binary(tmp_path, exit_code=exit_code, stderr=stderr)
    test_dir = _make_sv_tree(tmp_path, metadata=metadata)
    return _run_over_tree(test_dir, binary, extra_args)


def test_all_pass_exit_zero(tmp_path: Path) -> None:
    assert _run_sv_tests(tmp_path, exit_code=0).returncode == 0


def test_all_pass_prints_pass(tmp_path: Path) -> None:
    assert "PASS" in _run_sv_tests(tmp_path, exit_code=0).stdout


def test_all_pass_prints_a_summary(tmp_path: Path) -> None:
    assert "summary" in _run_sv_tests(tmp_path, exit_code=0).stdout


def test_all_fail_exit_one(tmp_path: Path) -> None:
    assert _run_sv_tests(tmp_path, exit_code=1).returncode == 1


def test_all_fail_prints_fail(tmp_path: Path) -> None:
    assert "FAIL" in _run_sv_tests(tmp_path, exit_code=1).stdout


def test_expected_rejection_prints_the_stub_diagnostic(tmp_path: Path) -> None:
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
    result = _run_sv_tests(
        tmp_path,
        exit_code=-11,
        metadata="/*\n:should_fail_because: Variable redeclaration\n*/\n",
    )
    missing = [t for t in ("FAIL", "exited -11") if t not in result.stdout]
    assert not missing


def test_junit_xml_exit_code(tmp_path: Path) -> None:
    xml_path = str(tmp_path / "report.xml")
    result = _run_sv_tests(
        tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path]
    )
    assert result.returncode == 0


def test_junit_xml_writes_the_report(tmp_path: Path) -> None:
    xml_path = str(tmp_path / "report.xml")
    _run_sv_tests(tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path])
    assert Path(xml_path).exists()


def test_junit_xml_structure(tmp_path: Path) -> None:
    xml_path = str(tmp_path / "report.xml")
    _run_sv_tests(
        tmp_path, exit_code=0, extra_args=["--junit-xml", xml_path]
    )

    tree = ET.parse(xml_path)
    root = tree.getroot()
    assert (
        root.tag, root.attrib["tests"], root.attrib["failures"]
    ) == ("testsuite", "2", "0")


def _make_argv_recording_binary(tmp_path: Path, record: Path) -> Path:
    binary = tmp_path / "deltahdl"
    binary.write_text(
        f"#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> {record}\nexit 0\n"
    )
    binary.chmod(binary.stat().st_mode | stat.S_IEXEC)
    return binary


def _make_uvm_suite(tmp_path: Path) -> tuple[Path, Path, Path]:
    test_dir = _make_sv_tree(
        tmp_path, metadata="/*\n:name: t\n:tags: uvm-random uvm\n*/\n",
    )
    (test_dir.parent / "conf" / "runners" / "libs.json").write_text(
        '{"uvm": {"files": ["tests/uvm/src/uvm_pkg.sv"],'
        ' "incdirs": ["tests/uvm/src"]}}\n'
    )
    src = test_dir.parent / "third_party" / "tests" / "uvm" / "src"
    src.mkdir(parents=True)
    (src / "uvm_pkg.sv").write_text("package uvm_pkg; endpackage\n")
    return test_dir, src / "uvm_pkg.sv", src


def test_a_uvm_tagged_file_is_handed_the_suite_library(tmp_path: Path) -> None:
    test_dir, uvm_pkg, src = _make_uvm_suite(tmp_path)
    record = tmp_path / "argv.txt"
    binary = _make_argv_recording_binary(tmp_path, record)
    result = _run_over_tree(test_dir, binary)
    alpha = str(test_dir / "chapter-5" / "alpha.sv")
    argv = [
        line.split(" ") for line in record.read_text().splitlines()
        if line.endswith(alpha)
    ]
    assert (result.returncode, argv) == (
        0,
        [["--lint-only", "-D", "UVM_NO_DPI", f"+incdir+{src}", str(uvm_pkg), alpha]],
    )


def test_a_library_the_suite_names_but_lacks_stops_the_run(
    tmp_path: Path,
) -> None:
    test_dir, uvm_pkg, _ = _make_uvm_suite(tmp_path)
    uvm_pkg.unlink()
    record = tmp_path / "argv.txt"
    binary = _make_argv_recording_binary(tmp_path, record)
    result = _run_over_tree(test_dir, binary)
    assert (
        result.returncode, record.exists(), "library 'uvm' names" in result.stderr,
    ) == (1, False, True)


def test_summary_names_the_suite_commit(tmp_path: Path) -> None:
    binary = _make_stub_binary(tmp_path, exit_code=0)
    test_dir = _make_sv_tree(tmp_path, git_init=True)
    result = _run_over_tree(test_dir, binary)
    assert _head_commit(tmp_path) in result.stdout


def test_summary_reports_an_unknown_suite_revision_outside_a_repository(
    tmp_path: Path,
) -> None:
    result = _run_sv_tests(tmp_path, exit_code=0)
    assert "sv-tests revision: unknown" in result.stdout
