"""Tests for lib.python.satisfy.mutator (shared mutator infrastructure)."""

import argparse
import json
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

from lib.python.satisfy import SATISFIED, SubclauseDiagnostic
from lib.python.satisfy.mutator import (
    MUTATOR_DISALLOWED_TOOLS,
    add_dependencies_arg,
    add_diagnostic_file_arg,
    add_issue_arg,
    build_commit_message,
    build_mutator_parser,
    commit_mutator_result,
    filter_changes,
    format_diagnostic_summary,
    is_valid_path,
    load_diagnostic,
    parse_satisfied_dependencies,
    run_mutator_call,
)


# --- helpers ----------------------------------------------------------------


def _all_satisfied():
    """Return a fully satisfied diagnostic."""
    return SubclauseDiagnostic(
        rule_coverage=SATISFIED,
        test_coverage=SATISFIED,
        test_placement=SATISFIED,
        naming=SATISFIED,
        deduplication=SATISFIED,
    )


def _failing_diagnostic():
    """Return a diagnostic with one rule_coverage failure."""
    return SubclauseDiagnostic(
        rule_coverage=["rule 7 has no production code"],
        test_coverage=SATISFIED,
        test_placement=SATISFIED,
        naming=SATISFIED,
        deduplication=SATISFIED,
    )


# --- MUTATOR_DISALLOWED_TOOLS -----------------------------------------------


def test_disallowed_tools_blocks_git() -> None:
    """The mutator disallowed-tools list blocks all git invocations."""
    assert "Bash(git *)" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_gh() -> None:
    """The mutator disallowed-tools list blocks all gh invocations."""
    assert "Bash(gh *)" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_pytest() -> None:
    """The mutator disallowed-tools list blocks pytest."""
    assert "Bash(pytest *)" in MUTATOR_DISALLOWED_TOOLS


def test_disallowed_tools_blocks_cmake() -> None:
    """The mutator disallowed-tools list blocks cmake."""
    assert "Bash(cmake *)" in MUTATOR_DISALLOWED_TOOLS


# --- argparse helpers -------------------------------------------------------


def test_add_diagnostic_file_arg_required() -> None:
    """--diagnostic-file is required."""
    parser = argparse.ArgumentParser()
    add_diagnostic_file_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])


def test_add_diagnostic_file_arg_value() -> None:
    """--diagnostic-file accepts a path string."""
    parser = argparse.ArgumentParser()
    add_diagnostic_file_arg(parser)
    args = parser.parse_args(["--diagnostic-file", "/tmp/diag.json"])
    assert args.diagnostic_file == Path("/tmp/diag.json")


def test_add_issue_arg_required() -> None:
    """--issue is required."""
    parser = argparse.ArgumentParser()
    add_issue_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])


def test_add_issue_arg_int_value() -> None:
    """--issue parses to an int."""
    parser = argparse.ArgumentParser()
    add_issue_arg(parser)
    args = parser.parse_args(["--issue", "42"])
    assert args.issue == 42


def test_add_dependencies_arg_default() -> None:
    """--satisfied-dependencies defaults to an empty string."""
    parser = argparse.ArgumentParser()
    add_dependencies_arg(parser)
    args = parser.parse_args([])
    assert args.satisfied_dependencies == ""


def test_add_dependencies_arg_value() -> None:
    """--satisfied-dependencies accepts a comma-separated list."""
    parser = argparse.ArgumentParser()
    add_dependencies_arg(parser)
    args = parser.parse_args([
        "--satisfied-dependencies", "33.4.1,33.4.2",
    ])
    assert args.satisfied_dependencies == "33.4.1,33.4.2"


# --- load_diagnostic --------------------------------------------------------


def _write_diag(tmp_path, payload):
    """Write *payload* as JSON and return the path."""
    path = tmp_path / "diag.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def test_load_diagnostic_all_satisfied(tmp_path) -> None:
    """A fully-satisfied diagnostic loads with verdict 'yes'."""
    payload = {
        "rule_coverage": SATISFIED,
        "test_coverage": SATISFIED,
        "test_placement": SATISFIED,
        "naming": SATISFIED,
        "deduplication": SATISFIED,
    }
    diag = load_diagnostic(_write_diag(tmp_path, payload))
    assert diag.verdict == "yes"


def test_load_diagnostic_with_failures(tmp_path) -> None:
    """A diagnostic with failures loads them verbatim."""
    payload = {
        "rule_coverage": ["rule 7 has no production code"],
        "test_coverage": SATISFIED,
        "test_placement": SATISFIED,
        "naming": SATISFIED,
        "deduplication": SATISFIED,
    }
    diag = load_diagnostic(_write_diag(tmp_path, payload))
    assert diag.rule_coverage == ["rule 7 has no production code"]


def test_load_diagnostic_rejects_missing_condition(tmp_path) -> None:
    """A diagnostic missing a condition is rejected."""
    payload = {
        "rule_coverage": SATISFIED,
        "test_coverage": SATISFIED,
        "test_placement": SATISFIED,
        "naming": SATISFIED,
        # deduplication missing
    }
    with pytest.raises(ValueError):
        load_diagnostic(_write_diag(tmp_path, payload))


# --- format_diagnostic_summary ----------------------------------------------


def test_format_diagnostic_summary_all_satisfied() -> None:
    """A fully-satisfied diagnostic formats with five 'satisfied' lines."""
    text = format_diagnostic_summary(_all_satisfied())
    assert text.count("satisfied") == 5


def test_format_diagnostic_summary_lists_failures() -> None:
    """A failure list appears as bullet points under its condition."""
    text = format_diagnostic_summary(_failing_diagnostic())
    assert "rule 7 has no production code" in text


def test_format_diagnostic_summary_names_failing_condition() -> None:
    """The failing condition name appears in the formatted summary."""
    text = format_diagnostic_summary(_failing_diagnostic())
    assert "rule_coverage" in text


# --- parse_satisfied_dependencies ------------------------------------------


def test_parse_satisfied_dependencies_empty() -> None:
    """An empty string parses to an empty list."""
    assert parse_satisfied_dependencies("") == []


def test_parse_satisfied_dependencies_single() -> None:
    """A single value parses to a one-element list."""
    assert parse_satisfied_dependencies("33.4.1") == ["33.4.1"]


def test_parse_satisfied_dependencies_multiple() -> None:
    """A comma-separated list parses to multiple elements."""
    assert parse_satisfied_dependencies("33.4.1,33.4.2") == [
        "33.4.1", "33.4.2",
    ]


def test_parse_satisfied_dependencies_strips_whitespace() -> None:
    """Whitespace around entries is stripped."""
    assert parse_satisfied_dependencies("33.4.1, 33.4.2") == [
        "33.4.1", "33.4.2",
    ]


def test_parse_satisfied_dependencies_skips_blanks() -> None:
    """Empty fragments between commas are dropped."""
    assert parse_satisfied_dependencies("33.4.1,,33.4.2") == [
        "33.4.1", "33.4.2",
    ]


# --- run_mutator_call -------------------------------------------------------


def _patched_run(returncode=0):
    """Patch subprocess.run with a CompletedProcess at *returncode*."""
    completed = MagicMock()
    completed.returncode = returncode
    return patch(
        "lib.python.satisfy.mutator.subprocess.run",
        return_value=completed,
    )


def test_run_mutator_call_passes_prompt() -> None:
    """run_mutator_call passes the prompt as subprocess input."""
    with _patched_run() as mock_run:
        run_mutator_call("hello prompt", model="opus")
    assert mock_run.call_args[1]["input"] == "hello prompt"


def test_run_mutator_call_passes_model() -> None:
    """run_mutator_call passes --model to the Claude CLI."""
    with _patched_run() as mock_run:
        run_mutator_call("prompt", model="haiku")
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--model") + 1] == "haiku"


def test_run_mutator_call_passes_disallowed_tools() -> None:
    """run_mutator_call passes --disallowedTools."""
    with _patched_run() as mock_run:
        run_mutator_call("prompt", model="opus")
    assert "--disallowedTools" in mock_run.call_args[0][0]


def test_run_mutator_call_uses_dangerously_skip_permissions() -> None:
    """run_mutator_call passes --dangerously-skip-permissions."""
    with _patched_run() as mock_run:
        run_mutator_call("prompt", model="opus")
    assert "--dangerously-skip-permissions" in mock_run.call_args[0][0]


def test_run_mutator_call_exits_on_nonzero() -> None:
    """A non-zero exit code is loud-fatal."""
    with _patched_run(returncode=2):
        with pytest.raises(SystemExit):
            run_mutator_call("prompt", model="opus")


def test_run_mutator_call_dumps_message_on_nonzero(capsys) -> None:
    """A non-zero exit prints an error to stderr."""
    with _patched_run(returncode=2):
        try:
            run_mutator_call("prompt", model="opus")
        except SystemExit:
            pass
    assert "code 2" in capsys.readouterr().err


# --- is_valid_path ----------------------------------------------------------


def test_is_valid_path_cpp() -> None:
    """A .cpp file is a valid path."""
    assert is_valid_path("src/foo.cpp") is True


def test_is_valid_path_h() -> None:
    """A .h file is a valid path."""
    assert is_valid_path("src/foo.h") is True


def test_is_valid_path_py() -> None:
    """A .py file is a valid path."""
    assert is_valid_path("scripts/foo.py") is True


def test_is_valid_path_cmakelists() -> None:
    """CMakeLists.txt is a valid path."""
    assert is_valid_path("test/CMakeLists.txt") is True


def test_is_valid_path_garbage() -> None:
    """A garbage entry is rejected."""
    assert is_valid_path("{a,") is False


def test_is_valid_path_no_extension() -> None:
    """A path with no recognised extension is rejected."""
    assert is_valid_path("README") is False


# --- filter_changes ---------------------------------------------------------


def test_filter_changes_keeps_valid() -> None:
    """filter_changes preserves entries with valid extensions."""
    added, _modified, _deleted = filter_changes(
        (["a.cpp", "junk"], [], []),
    )
    assert added == ["a.cpp"]


def test_filter_changes_drops_invalid_modified() -> None:
    """filter_changes drops invalid entries from modified."""
    _added, modified, _deleted = filter_changes(
        ([], ["b.h", "junk"], []),
    )
    assert modified == ["b.h"]


def test_filter_changes_drops_invalid_deleted() -> None:
    """filter_changes drops invalid entries from deleted."""
    _added, _modified, deleted = filter_changes(
        ([], [], ["c.py", "junk"]),
    )
    assert deleted == ["c.py"]


# --- build_commit_message ---------------------------------------------------


def test_build_commit_message_single_subclause_title() -> None:
    """A single-subclause commit title uses 'Satisfy §X' format."""
    msg = build_commit_message(["6.3"], [42], "- Modified foo.cpp")
    assert "Satisfy §6.3" in msg


def test_build_commit_message_set_title() -> None:
    """A multi-subclause commit title names cycle co-implementation."""
    msg = build_commit_message(["33.4.1.5", "33.4.1.6"], [10, 11], "")
    assert "cycle co-implementation" in msg


def test_build_commit_message_includes_summary() -> None:
    """The commit message includes the file-change summary body."""
    msg = build_commit_message(["6.3"], [42], "- Modified foo.cpp")
    assert "- Modified foo.cpp" in msg


def test_build_commit_message_includes_single_closes() -> None:
    """A single-subclause message includes one Closes trailer."""
    msg = build_commit_message(["6.3"], [42], "")
    assert "Closes #42" in msg


def test_build_commit_message_includes_multiple_closes() -> None:
    """A multi-subclause message includes one Closes trailer per issue."""
    msg = build_commit_message(["33.4.1.5", "33.4.1.6"], [10, 11], "")
    assert msg.count("Closes #") == 2


def test_build_commit_message_uses_annex_label() -> None:
    """Annex subclauses appear with their letter prefix (no §)."""
    msg = build_commit_message(["A.7.1"], [42], "")
    assert "Satisfy A.7.1" in msg


# --- commit_mutator_result --------------------------------------------------


def _patched_porcelain(changes):
    """Patch get_porcelain_changes with a fixed return value."""
    return patch(
        "lib.python.satisfy.mutator.get_porcelain_changes",
        return_value=changes,
    )


def _patched_commit():
    """Patch commit_and_push with a no-op MagicMock."""
    return patch(
        "lib.python.satisfy.mutator.commit_and_push",
        return_value="abc123",
    )


def test_commit_mutator_result_returns_false_when_clean() -> None:
    """commit_mutator_result returns False when the working tree is clean."""
    with _patched_porcelain(([], [], [])), _patched_commit() as mock_c:
        result = commit_mutator_result(["6.3"], [42])
    assert (result, mock_c.called) == (False, False)


def test_commit_mutator_result_returns_true_when_dirty() -> None:
    """commit_mutator_result returns True when porcelain has source files."""
    with _patched_porcelain((["foo.cpp"], [], [])), _patched_commit():
        result = commit_mutator_result(["6.3"], [42])
    assert result is True


def test_commit_mutator_result_calls_commit_and_push() -> None:
    """commit_mutator_result invokes commit_and_push with the file list."""
    with _patched_porcelain((["foo.cpp"], ["bar.h"], [])), \
            _patched_commit() as mock_c:
        commit_mutator_result(["6.3"], [42])
    assert mock_c.call_args[0][0] == ["foo.cpp", "bar.h"]


def test_commit_mutator_result_filters_garbage_added() -> None:
    """commit_mutator_result drops garbage paths from added before commit."""
    with _patched_porcelain((["foo.cpp", "{a,"], [], [])), \
            _patched_commit() as mock_c:
        commit_mutator_result(["6.3"], [42])
    assert mock_c.call_args[0][0] == ["foo.cpp"]


def test_commit_mutator_result_filters_garbage_deleted() -> None:
    """commit_mutator_result drops garbage paths from deleted before commit."""
    with _patched_porcelain(([], [], ["foo.cpp", "{a,"])), \
            _patched_commit() as mock_c:
        commit_mutator_result(["6.3"], [42])
    assert mock_c.call_args[0][1] == ["foo.cpp"]


def test_commit_mutator_result_returns_false_when_only_garbage() -> None:
    """commit_mutator_result returns False when porcelain is only garbage."""
    with _patched_porcelain((["{a,"], [], [])), _patched_commit() as mock_c:
        result = commit_mutator_result(["6.3"], [42])
    assert (result, mock_c.called) == (False, False)


# --- build_mutator_parser ---------------------------------------------------


def _make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


def test_build_mutator_parser_accepts_full_arg_set(tmp_path) -> None:
    """build_mutator_parser wires up subclause/diagnostic/issue/lrm/model."""
    parser = build_mutator_parser("test")
    args = parser.parse_args([
        "--lrm", str(_make_lrm(tmp_path)),
        "--subclause", "6.3",
        "--diagnostic-file", "/tmp/d.json",
        "--issue", "42",
        "--model", "haiku",
    ])
    assert (args.subclause, args.issue, args.model) == ("6.3", 42, "haiku")


def test_build_mutator_parser_diagnostic_file_required(tmp_path) -> None:
    """build_mutator_parser makes --diagnostic-file required."""
    parser = build_mutator_parser("test")
    with pytest.raises(SystemExit):
        parser.parse_args([
            "--lrm", str(_make_lrm(tmp_path)),
            "--subclause", "6.3",
            "--issue", "42",
        ])


def test_build_mutator_parser_issue_required(tmp_path) -> None:
    """build_mutator_parser makes --issue required."""
    parser = build_mutator_parser("test")
    with pytest.raises(SystemExit):
        parser.parse_args([
            "--lrm", str(_make_lrm(tmp_path)),
            "--subclause", "6.3",
            "--diagnostic-file", "/tmp/d.json",
        ])
