"""Unit tests for implement_subclause."""

import argparse
import subprocess
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest


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


# ---- _lrm_labels_for_subclause --------------------------------------------


_LRM_MULTI_SUBCLAUSE = """\
4. Scheduling semantics
Table 4-1\u2014PLI callbacks

4.1 General
General text.
Figure 4-1\u2014Overview diagram

4.2 Events
Table 4-2\u2014Event types

4.3 Other
No figures or tables.

5. Data types
"""


def test_lrm_labels_subclause_has_no_refs(isc, tmp_path):
    """Returns empty lists when subclause has no figure/table refs."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_MULTI_SUBCLAUSE)
    assert isc._lrm_labels_for_subclause(lrm, "4.3") == ([], [])


def test_lrm_labels_subclause_finds_table(isc, tmp_path):
    """Finds table labels scoped to the target subclause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_MULTI_SUBCLAUSE)
    assert isc._lrm_labels_for_subclause(lrm, "4.2") == ([], ["4-2"])


def test_lrm_labels_subclause_finds_figure(isc, tmp_path):
    """Finds figure labels scoped to the target subclause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_MULTI_SUBCLAUSE)
    assert isc._lrm_labels_for_subclause(lrm, "4.1") == (["4-1"], [])


# ---- format_prompt --------------------------------------------------------


def test_format_prompt_forbids_building(isc):
    """Prompt tells Claude not to build or run tests."""
    result = isc.format_prompt("4.1", "~/LRM.txt", ["4"], issue=6)
    assert "Do not build or run tests" in result


def test_format_prompt_includes_supplementary(isc):
    """Supplementary text appears in the formatted prompt."""
    result = isc.format_prompt(
        "4.1", "~/LRM.txt", ["4"],
        issue=6,
        supplementary="Consult Table 4-1 at /t (Markdown)"
        " when implementing.",
    )
    assert "Table 4-1" in result


# ---- find_context_subclauses ----------------------------------------------


def test_find_context_general(isc):
    """Finds sibling titled 'General'."""
    titles = {"4.1": "General", "4.2": "Foo"}
    assert isc.find_context_subclauses("4.3", titles) == ["4.1"]


def test_find_context_overview(isc):
    """Finds siblings titled 'General' and 'Overview'."""
    titles = {"4.1": "General", "4.2": "Overview", "4.3": "Foo"}
    assert isc.find_context_subclauses("4.3", titles) == ["4.1", "4.2"]


def test_find_context_none(isc):
    """Returns empty list when no General/Overview siblings exist."""
    titles = {"4.1": "Foo", "4.2": "Bar"}
    assert not isc.find_context_subclauses("4.1", titles)


def test_find_context_excludes_self(isc):
    """Does not include the target subclause itself."""
    titles = {"4.1": "General"}
    assert not isc.find_context_subclauses("4.1", titles)


def test_find_context_intermediate(isc):
    """Finds General at an intermediate ancestry level."""
    titles = {
        "4.1": "General",
        "4.4": "Foo",
        "4.4.1": "General",
        "4.4.3": "Bar",
    }
    assert isc.find_context_subclauses("4.4.3", titles) == [
        "4.1", "4.4.1",
    ]


def test_find_context_depth_1(isc):
    """Depth-1 clause has no siblings to scan."""
    titles = {"4.1": "General", "4.2": "Overview"}
    assert not isc.find_context_subclauses("4", titles)


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


@patch("implement_subclause.invoke_claude")
def test_run_prompt_calls_invoke(mock_invoke, isc, tmp_path):
    """run_prompt loads titles, builds prompt, and invokes Claude."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("4. Scheduling semantics\n4.1 General\n")
    build_fn = MagicMock(return_value="generated prompt")
    args = argparse.Namespace(
        lrm=lrm, subclause="4.1", issue=6,
        model="sonnet", continue_session=False,
    )
    isc.run_prompt(build_fn, args)
    assert mock_invoke.call_args[0][0] == "generated prompt"


@patch("implement_subclause.invoke_claude")
def test_run_prompt_passes_continue_session(mock_invoke, isc, tmp_path):
    """run_prompt passes continue_session to invoke_claude."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("4. Scheduling semantics\n4.1 General\n")
    build_fn = MagicMock(return_value="generated prompt")
    args = argparse.Namespace(
        lrm=lrm, subclause="4.1", issue=6,
        model="sonnet", continue_session=True,
    )
    isc.run_prompt(build_fn, args)
    assert mock_invoke.call_args[1]["continue_session"] is True
