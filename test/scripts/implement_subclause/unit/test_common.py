"""Unit tests for implement_subclause."""

import argparse
import inspect
from unittest.mock import MagicMock, patch


# ---- build_hierarchy --------------------------------------------------------


class TestBuildHierarchyNumeric:
    """Tests for numeric (non-annex) clauses."""

    def test_depth_1(self, isc):
        """Clause '4' produces depth-1 numeric hierarchy."""
        assert isc.build_hierarchy("4") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4",
        }

    def test_depth_2(self, isc):
        """Clause '4.1' produces depth-2 numeric hierarchy."""
        assert isc.build_hierarchy("4.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4.1",
        }

    def test_depth_3(self, isc):
        """Clause '6.24.1' produces depth-3 numeric hierarchy."""
        assert isc.build_hierarchy("6.24.1") == {
            "is_annex": False,
            "clause_number": "6",
            "ancestors": ["6.24"],
            "subclause": "6.24.1",
        }

    def test_depth_4(self, isc):
        """Clause '4.4.3.1' produces depth-4 numeric hierarchy."""
        assert isc.build_hierarchy("4.4.3.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": ["4.4", "4.4.3"],
            "subclause": "4.4.3.1",
        }

    def test_depth_5(self, isc):
        """Clause '4.4.3.1.2' produces depth-5 numeric hierarchy."""
        assert isc.build_hierarchy("4.4.3.1.2") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": ["4.4", "4.4.3", "4.4.3.1"],
            "subclause": "4.4.3.1.2",
        }


class TestBuildHierarchyAnnex:
    """Tests for annex (uppercase letter) clauses."""

    def test_depth_1(self, isc):
        """Clause 'B' produces depth-1 annex hierarchy."""
        assert isc.build_hierarchy("B") == {
            "is_annex": True,
            "collection": "Annex B",
            "letter": "B",
            "ancestors": [],
            "subclause": "B",
        }

    def test_depth_2(self, isc):
        """Clause 'A.8' produces depth-2 annex hierarchy."""
        assert isc.build_hierarchy("A.8") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": [],
            "subclause": "A.8",
        }

    def test_depth_3(self, isc):
        """Clause 'A.8.1' produces depth-3 annex hierarchy."""
        assert isc.build_hierarchy("A.8.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.8"],
            "subclause": "A.8.1",
        }

    def test_depth_4(self, isc):
        """Clause 'A.7.5.3' produces depth-4 annex hierarchy."""
        assert isc.build_hierarchy("A.7.5.3") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.7", "A.7.5"],
            "subclause": "A.7.5.3",
        }

    def test_depth_5(self, isc):
        """Clause 'A.7.5.3.1' produces depth-5 annex hierarchy."""
        assert isc.build_hierarchy("A.7.5.3.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.7", "A.7.5", "A.7.5.3"],
            "subclause": "A.7.5.3.1",
        }


# ---- format_prompt --------------------------------------------------------


def test_format_prompt_forbids_building(isc):
    """Prompt tells Claude not to build or run tests."""
    result = isc.format_prompt("4.1", "~/LRM.txt", issue=6)
    assert "Do not build or run tests" in result


def test_format_prompt_no_supplementary_param(isc):
    """format_prompt does not accept a supplementary parameter."""
    sig = inspect.signature(isc.format_prompt)
    assert "supplementary" not in sig.parameters


def test_format_prompt_mentions_general(isc):
    """Prompt instructs Claude to read General sections."""
    result = isc.format_prompt("4.4.3", "~/LRM.txt", issue=6)
    assert "General" in result


def test_format_prompt_mentions_overview(isc):
    """Prompt instructs Claude to read Overview sections."""
    result = isc.format_prompt("4.4.3", "~/LRM.txt", issue=6)
    assert "Overview" in result


def test_format_prompt_scope_constraint(isc):
    """Prompt constrains Claude to only implement the requested subclause."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "Only implement §10.10.2" in result


def test_format_prompt_elaborator_test_filename(isc):
    """Prompt includes elaborator subclause-specific test filename."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "test_elaborator_clause_10_10_02.cpp" in result


def test_format_prompt_simulator_test_filename(isc):
    """Prompt includes simulator subclause-specific test filename."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "test_simulator_clause_10_10_02.cpp" in result


def test_format_prompt_forbids_parent_file(isc):
    """Prompt forbids putting tests in parent clause file."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "parent clause file" in result


def test_format_prompt_search_for_misplaced_tests(isc):
    """Prompt instructs Claude to search test/src/unit/ for misplaced tests."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "Search test/src/unit/" in result


def test_format_prompt_search_mentions_subclause(isc):
    """Misplaced-test search instruction references the target subclause."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "§10.10.2" in result


def test_format_prompt_forbids_git_commits(isc):
    """Prompt forbids making git commits."""
    result = isc.format_prompt("10.10.2", "~/LRM.txt", issue=6)
    assert "Do not make git commits" in result


# ---- invoke_claude --------------------------------------------------------


def test_invoke_claude_passes_verbose(isc, popen_ok):
    """invoke_claude includes --verbose in the CLI command."""
    isc.invoke_claude("test prompt", model="opus")
    assert "--verbose" in popen_ok.call_args[0][0]


def test_invoke_claude_uses_print_mode(isc, popen_ok):
    """invoke_claude uses -p (print mode)."""
    isc.invoke_claude("test prompt", model="opus")
    assert "-p" in popen_ok.call_args[0][0]


def test_invoke_claude_uses_stream_json(isc, popen_ok):
    """invoke_claude uses --output-format stream-json for real-time output."""
    isc.invoke_claude("test prompt", model="opus")
    cmd = popen_ok.call_args[0][0]
    idx = cmd.index("--output-format")
    assert cmd[idx + 1] == "stream-json"


def test_invoke_claude_uses_dangerously_skip_permissions(isc, popen_ok):
    """invoke_claude uses --dangerously-skip-permissions."""
    isc.invoke_claude("test prompt", model="opus")
    assert "--dangerously-skip-permissions" in popen_ok.call_args[0][0]


def test_invoke_claude_no_continue_by_default(isc, popen_ok):
    """invoke_claude does not include --continue by default."""
    isc.invoke_claude("test prompt", model="opus")
    assert "--continue" not in popen_ok.call_args[0][0]


def test_invoke_claude_uses_continue_when_set(isc, popen_ok):
    """invoke_claude includes --continue when continue_session=True."""
    isc.invoke_claude("test prompt", model="opus", continue_session=True)
    assert "--continue" in popen_ok.call_args[0][0]


def test_invoke_claude_success(isc, popen_ok):
    """invoke_claude streams prompt to Claude CLI and returns on success."""
    isc.invoke_claude("test prompt", model="opus")
    assert popen_ok.return_value.communicate.called


@patch("implement_subclause.sys.exit")
@patch("implement_subclause.subprocess.Popen")
def test_invoke_claude_failure_exits(mock_popen, mock_exit, isc):
    """invoke_claude calls sys.exit on non-zero return code."""
    proc = MagicMock()
    proc.communicate.return_value = (None, None)
    proc.returncode = 1
    proc.__enter__ = MagicMock(return_value=proc)
    proc.__exit__ = MagicMock(return_value=False)
    mock_popen.return_value = proc
    isc.invoke_claude("test prompt")
    assert mock_exit.called


# ---- run_prompt -----------------------------------------------------------


def _run_prompt_and_capture(isc, tmp_path):
    """Helper: invoke run_prompt with a mock build_fn and return (mock_invoke, build_fn)."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    build_fn = MagicMock(return_value="generated prompt")
    args = argparse.Namespace(
        lrm=lrm, subclause="4.1", issue=6,
        model="opus", continue_session=False,
    )
    with patch("implement_subclause.invoke_claude") as mock_invoke:
        isc.run_prompt(build_fn, args)
    return mock_invoke, build_fn


def test_run_prompt_calls_invoke(isc, tmp_path):
    """run_prompt builds prompt and invokes Claude."""
    mock_invoke, _ = _run_prompt_and_capture(isc, tmp_path)
    assert mock_invoke.call_args[0][0] == "generated prompt"


def test_run_prompt_does_not_load_titles(isc, tmp_path):
    """run_prompt passes only positional args (subclause, lrm_path)."""
    _, build_fn = _run_prompt_and_capture(isc, tmp_path)
    assert len(build_fn.call_args[0]) == 2  # subclause, lrm_path


def test_run_prompt_passes_subclause(isc, tmp_path):
    """run_prompt passes the subclause as the first positional arg."""
    _, build_fn = _run_prompt_and_capture(isc, tmp_path)
    assert build_fn.call_args[0][0] == "4.1"


@patch("implement_subclause.invoke_claude")
def test_run_prompt_passes_continue_session(mock_invoke, isc, tmp_path):
    """run_prompt passes continue_session to invoke_claude."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    build_fn = MagicMock(return_value="generated prompt")
    args = argparse.Namespace(
        lrm=lrm, subclause="4.1", issue=6,
        model="opus", continue_session=True,
    )
    isc.run_prompt(build_fn, args)
    assert mock_invoke.call_args[1]["continue_session"] is True


def test_invoke_claude_passes_effort_high(isc, popen_ok):
    """invoke_claude includes --effort high in the CLI command."""
    isc.invoke_claude("test prompt", model="opus")
    cmd = popen_ok.call_args[0][0]
    idx = cmd.index("--effort")
    assert cmd[idx + 1] == "high"
