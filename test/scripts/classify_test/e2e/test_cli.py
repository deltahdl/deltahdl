"""End-to-end tests for the classify_test CLI."""

import json
import os
import stat
import subprocess
import sys
from pathlib import Path

_SCRIPTS_DIR = str(
    Path(__file__).resolve().parents[4] / "scripts",
)


# ---- Helpers ---------------------------------------------------------------


def _invoke(*args, cwd=None, env=None):
    """Run classify_test in a child process."""
    run_env = (env or os.environ).copy()
    pypath = run_env.get("PYTHONPATH", "")
    run_env["PYTHONPATH"] = (
        _SCRIPTS_DIR + os.pathsep + pypath if pypath else _SCRIPTS_DIR
    )
    return subprocess.run(
        [sys.executable, "-m", "classify_test", *args],
        capture_output=True,
        text=True,
        cwd=cwd,
        env=run_env,
        check=False,
    )


def _bootstrap_repo(tmp_path, cmake_body="# header\n"):
    """Create minimal repo layout so find_repo_root succeeds."""
    (tmp_path / "test").mkdir()
    (tmp_path / "test" / "CMakeLists.txt").write_text(
        cmake_body, encoding="utf-8",
    )


def _create_ref_files(tmp_path):
    """Create minimal LRM file for --lrm flag."""
    lrm = tmp_path / "LRM.txt"
    lrm.write_text("1 Overview\n", encoding="utf-8")
    return str(lrm)


def _base_env(tmp_path):
    """Build subprocess env with HOME pointing to *tmp_path*."""
    env = os.environ.copy()
    env["HOME"] = str(tmp_path)
    return env


def _install_fake(tmp_path, name, body):
    """Install a fake executable in tmp_path/bin; return bin dir."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir(exist_ok=True)
    script = bin_dir / name
    script.write_text(body, encoding="utf-8")
    script.chmod(script.stat().st_mode | stat.S_IEXEC)
    return bin_dir


def _env_with_fakes(tmp_path, claude_response):
    """Build env with fake claude and git binaries on PATH."""
    payload = json.dumps(claude_response)
    bin_dir = _install_fake(
        tmp_path, "claude",
        f"#!/bin/sh\necho '{payload}'\n",
    )
    _install_fake(tmp_path, "git", "#!/bin/sh\nexit 0\n")
    env = _base_env(tmp_path)
    env["PATH"] = str(bin_dir) + os.pathsep + env.get("PATH", "")
    return env


def _write_test_file(tmp_path, body):
    """Write test_input.cpp wrapping *body* in gtest boilerplate."""
    parts = [
        "#include <gtest/gtest.h>", "",
        "namespace {", "",
        body.rstrip(), "",
        "}  // namespace", "",
    ]
    f = tmp_path / "test_input.cpp"
    f.write_text("\n".join(parts), encoding="utf-8")
    return f


def _run_dry(tmp_path):
    """Bootstrap and execute a dry-run pipeline."""
    _bootstrap_repo(tmp_path)
    _write_test_file(tmp_path, "TEST(S, DryT) {\n  auto r = Parse(src);\n}")
    lrm = _create_ref_files(tmp_path)
    resp = {"clause": "6.1", "rationale": "r"}
    env = _env_with_fakes(tmp_path, resp)
    return _invoke(
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "DryT", "--dry-run",
        cwd=str(tmp_path), env=env,
    )


def _setup_pipeline(tmp_path):
    """Prepare repo, input, cmake, and fakes."""
    _bootstrap_repo(
        tmp_path, "# header\nadd_unit_test(test_input)\n",
    )
    _write_test_file(
        tmp_path,
        "TEST(S, Alpha) {\n  auto r = Parse(src);\n}",
    )
    lrm = _create_ref_files(tmp_path)
    resp = {"clause": "6.1", "rationale": "r"}
    return _env_with_fakes(tmp_path, resp), lrm


def _run_pipeline(tmp_path):
    """Run the full live pipeline and return CompletedProcess."""
    env, lrm = _setup_pipeline(tmp_path)
    return _invoke(
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "Alpha",
        cwd=str(tmp_path), env=env,
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage(tmp_path):
    """Running with no arguments prints usage to stderr."""
    _bootstrap_repo(tmp_path)
    assert "usage:" in _invoke(cwd=str(tmp_path)).stderr


def test_missing_file_flag_reported(tmp_path):
    """Omitting --file reports the missing argument."""
    _bootstrap_repo(tmp_path)
    assert "--file" in _invoke(
        "--output-dir", str(tmp_path), cwd=str(tmp_path),
    ).stderr


def test_missing_output_dir_flag_reported(tmp_path):
    """Omitting --output-dir reports the missing argument."""
    _bootstrap_repo(tmp_path)
    assert "--output-dir" in _invoke(
        "--file", "f.cpp", cwd=str(tmp_path),
    ).stderr


# ---- Input validation errors -----------------------------------------------


def test_nonexistent_file_reports_error(tmp_path):
    """Pointing --file at a missing path prints ERROR."""
    _bootstrap_repo(tmp_path)
    lrm = _create_ref_files(tmp_path)
    assert "ERROR" in _invoke(
        "--file", str(tmp_path / "missing.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "T",
        cwd=str(tmp_path), env=_base_env(tmp_path),
    ).stdout


def test_file_without_tests_reports_error(tmp_path):
    """A file with no TEST blocks prints an error about missing tests."""
    _bootstrap_repo(tmp_path)
    lrm = _create_ref_files(tmp_path)
    (tmp_path / "empty.cpp").write_text(
        "#include <gtest/gtest.h>\nint x = 0;\n",
        encoding="utf-8",
    )
    assert "No TEST blocks" in _invoke(
        "--file", str(tmp_path / "empty.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "T",
        cwd=str(tmp_path), env=_base_env(tmp_path),
    ).stdout


def test_test_not_found_reports_error(tmp_path):
    """Passing --test with unknown name prints ERROR."""
    _bootstrap_repo(tmp_path)
    _write_test_file(tmp_path, "TEST(S, Alpha) {\n}")
    lrm = _create_ref_files(tmp_path)
    assert "ERROR" in _invoke(
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "NoSuchTest",
        cwd=str(tmp_path), env=_base_env(tmp_path),
    ).stdout


# ---- Dry run ---------------------------------------------------------------


def test_dry_run_reports_completion(tmp_path):
    """Dry run output includes the dry run marker."""
    out = _run_dry(tmp_path).stdout
    assert "dry run" in out


def test_dry_run_lists_target_filename(tmp_path):
    """Dry run output lists the target filename."""
    assert "test_parser_clause_06_01.cpp" in _run_dry(tmp_path).stdout


def test_dry_run_does_not_create_output(tmp_path):
    """Dry run does not create any clause output files."""
    _run_dry(tmp_path)
    assert not (tmp_path / "test_parser_clause_06_01.cpp").exists()


# ---- Full pipeline ---------------------------------------------------------


def test_pipeline_reports_done(tmp_path):
    """Full pipeline prints CMakeLists.txt update message."""
    assert "Updated `CMakeLists.txt`" in _run_pipeline(tmp_path).stdout


def test_pipeline_creates_clause_file(tmp_path):
    """Pipeline creates the expected clause output file."""
    _run_pipeline(tmp_path)
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_pipeline_output_contains_test(tmp_path):
    """Generated clause file contains the classified test."""
    _run_pipeline(tmp_path)
    assert "TEST(S, Alpha)" in (
        tmp_path / "test_parser_clause_06_01.cpp"
    ).read_text()


def test_pipeline_deletes_input(tmp_path):
    """Pipeline removes the original input file."""
    _run_pipeline(tmp_path)
    assert not (tmp_path / "test_input.cpp").exists()


def test_pipeline_adds_cmake_entry(tmp_path):
    """CMakeLists.txt contains the new clause entry."""
    _run_pipeline(tmp_path)
    assert "test_parser_clause_06_01" in (
        tmp_path / "test" / "CMakeLists.txt"
    ).read_text()


def test_pipeline_drops_old_cmake_entry(tmp_path):
    """CMakeLists.txt no longer contains the old test_input entry."""
    _run_pipeline(tmp_path)
    assert "test_input" not in (
        tmp_path / "test" / "CMakeLists.txt"
    ).read_text()


# ---- Named namespace wrapper -----------------------------------------------


def _setup_named_ns_pipeline(tmp_path):
    """Prepare repo with a test file using namespace delta { ... }."""
    _bootstrap_repo(
        tmp_path, "# header\nadd_unit_test(test_input)\n",
    )
    src = tmp_path / "test_input.cpp"
    src.write_text(
        "#include <gtest/gtest.h>\n"
        "\n"
        "namespace delta {\n"
        "namespace {\n"
        "\n"
        "TEST(S, Alpha) {\n"
        "  auto r = Parse(src);\n"
        "}\n"
        "\n"
        "}  // namespace\n"
        "}  // namespace delta\n",
        encoding="utf-8",
    )
    lrm = _create_ref_files(tmp_path)
    resp = {"clause": "6.1", "rationale": "r"}
    return _env_with_fakes(tmp_path, resp), lrm


def test_named_ns_pipeline_reports_done(tmp_path):
    """Pipeline succeeds on a file with named namespace wrapper."""
    env, lrm = _setup_named_ns_pipeline(tmp_path)
    r = _invoke(
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "Alpha",
        cwd=str(tmp_path), env=env,
    )
    assert "Updated `CMakeLists.txt`" in r.stdout


def _run_named_ns_pipeline(tmp_path):
    """Setup and run the named-namespace pipeline."""
    env, lrm = _setup_named_ns_pipeline(tmp_path)
    return _invoke(
        "--file", str(tmp_path / "test_input.cpp"),
        "--output-dir", str(tmp_path),
        "--lrm", lrm,
        "--test", "Alpha",
        cwd=str(tmp_path), env=env,
    )


def test_named_ns_pipeline_creates_clause_file(tmp_path):
    """Pipeline creates clause file from named-namespace input."""
    _run_named_ns_pipeline(tmp_path)
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_named_ns_pipeline_output_contains_test(tmp_path):
    """Clause file from named-namespace input contains the test."""
    _run_named_ns_pipeline(tmp_path)
    assert "TEST(S, Alpha)" in (
        tmp_path / "test_parser_clause_06_01.cpp"
    ).read_text()


# ---- Exit codes ------------------------------------------------------------


def test_dry_run_exits_zero(tmp_path):
    """Successful dry run exits with code 0."""
    assert _run_dry(tmp_path).returncode == 0


def test_pipeline_exits_zero(tmp_path):
    """Successful full pipeline exits with code 0."""
    assert _run_pipeline(tmp_path).returncode == 0
