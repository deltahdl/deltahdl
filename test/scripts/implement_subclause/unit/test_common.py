"""Unit tests for implement_subclause."""

from unittest.mock import MagicMock, patch

import pytest

from implement_subclause.streaming import ContentFilterError
from lib.python.classify import build_hierarchy


# ---- build_hierarchy --------------------------------------------------------


class TestBuildHierarchyNumeric:
    """Tests for numeric (non-annex) clauses."""

    def test_depth_1(self):
        """Clause '4' produces depth-1 numeric hierarchy."""
        assert build_hierarchy("4") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4",
        }

    def test_depth_2(self):
        """Clause '4.1' produces depth-2 numeric hierarchy."""
        assert build_hierarchy("4.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4.1",
        }

    def test_depth_3(self):
        """Clause '6.24.1' produces depth-3 numeric hierarchy."""
        assert build_hierarchy("6.24.1") == {
            "is_annex": False,
            "clause_number": "6",
            "ancestors": ["6.24"],
            "subclause": "6.24.1",
        }

    def test_depth_4(self):
        """Clause '4.4.3.1' produces depth-4 numeric hierarchy."""
        assert build_hierarchy("4.4.3.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": ["4.4", "4.4.3"],
            "subclause": "4.4.3.1",
        }

    def test_depth_5(self):
        """Clause '4.4.3.1.2' produces depth-5 numeric hierarchy."""
        assert build_hierarchy("4.4.3.1.2") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": ["4.4", "4.4.3", "4.4.3.1"],
            "subclause": "4.4.3.1.2",
        }


class TestBuildHierarchyAnnex:
    """Tests for annex (uppercase letter) clauses."""

    def test_depth_1(self):
        """Clause 'B' produces depth-1 annex hierarchy."""
        assert build_hierarchy("B") == {
            "is_annex": True,
            "collection": "Annex B",
            "letter": "B",
            "ancestors": [],
            "subclause": "B",
        }

    def test_depth_2(self):
        """Clause 'A.8' produces depth-2 annex hierarchy."""
        assert build_hierarchy("A.8") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": [],
            "subclause": "A.8",
        }

    def test_depth_3(self):
        """Clause 'A.8.1' produces depth-3 annex hierarchy."""
        assert build_hierarchy("A.8.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.8"],
            "subclause": "A.8.1",
        }

    def test_depth_4(self):
        """Clause 'A.7.5.3' produces depth-4 annex hierarchy."""
        assert build_hierarchy("A.7.5.3") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.7", "A.7.5"],
            "subclause": "A.7.5.3",
        }

    def test_depth_5(self):
        """Clause 'A.7.5.3.1' produces depth-5 annex hierarchy."""
        assert build_hierarchy("A.7.5.3.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.7", "A.7.5", "A.7.5.3"],
            "subclause": "A.7.5.3.1",
        }


# ---- build_steps -----------------------------------------------------------


def test_build_steps_returns_list(isc):
    """build_steps returns a list of (description, prompt) tuples."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert isinstance(steps, list)


def test_build_steps_has_8_steps(isc):
    """build_steps returns exactly 8 steps after audit-scope removal."""
    assert len(isc.build_steps("4.1", "~/LRM.txt")) == 8


def test_build_steps_first_mentions_lrm(isc):
    """First step prompt embeds the LRM read instruction."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "LRM" in steps[0][1]


def test_build_steps_first_is_auditing_src(isc):
    """First step is Auditing src."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert steps[0][0] == "Auditing src"


def test_build_steps_last_is_implementing_functionality(isc):
    """Last step is Implementing missing functionality."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert steps[-1][0] == "Implementing missing functionality"


def test_build_steps_each_has_description(isc):
    """Each step has a non-empty description."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert all(desc for desc, _ in steps)


def test_build_steps_delete_step_scoped_to_subclause(isc):
    """Delete duplicates step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[2][1]


def test_build_steps_rename_suites_scoped_to_subclause(isc):
    """Rename suites step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[4][1]


def test_build_steps_rename_tests_scoped_to_subclause(isc):
    """Rename tests step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[5][1]


def test_build_steps_exclude_appears_in_step(isc):
    """Exclude subclauses appear in a step prompt."""
    steps = isc.build_steps("15.3", "~/LRM.txt", exclude="15.3.1")
    prompts = " ".join(p for _, p in steps)
    assert "15.3.1" in prompts


def test_build_steps_constraints_include_directly_defined(isc):
    """Constraints mention only directly defined requirements."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    prompts = " ".join(p for _, p in steps)
    assert "directly defined" in prompts


def test_build_steps_no_implementability_step(isc):
    """No 'Checking implementability' step exists after gate removal."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert all(desc != "Checking implementability" for desc, _ in steps)


# ---- run_steps -------------------------------------------------------------


def _run_steps_with_ok_mock(isc):
    """Build steps, stub run_claude_streaming with success, return (mock, result)."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    mock_streaming = MagicMock(return_value="- Done because needed")
    with patch("implement_subclause.run_claude_streaming", mock_streaming):
        result = isc.run_steps(steps, model="opus")
    return mock_streaming, result


def test_run_steps_call_count(isc):
    """run_steps calls run_claude_streaming 8 times (once per step)."""
    assert _run_steps_with_ok_mock(isc)[0].call_count == 8


def test_run_steps_returns_list_of_eight(isc):
    """run_steps returns an 8-element list after a successful run."""
    assert len(_run_steps_with_ok_mock(isc)[1]) == 8


def test_run_steps_returns_result_field(isc):
    """Each returned entry is the streaming helper's return value."""
    assert _run_steps_with_ok_mock(isc)[1][0] == "- Done because needed"


def test_run_steps_returns_result_for_all_steps(isc):
    """All 8 returned entries carry the streaming helper's return value."""
    results = _run_steps_with_ok_mock(isc)[1]
    assert all(entry == "- Done because needed" for entry in results)


def test_run_steps_uses_stream_json_format(isc):
    """run_steps requests stream-json output from the Claude CLI."""
    mock_streaming, _ = _run_steps_with_ok_mock(isc)
    cmd = mock_streaming.call_args_list[0][0][0]
    assert "stream-json" in cmd


def test_run_steps_prints_step_numbers(isc, capsys):
    """run_steps prints step numbers in stdout."""
    _run_steps_with_ok_mock(isc)
    assert "Step 1/8:" in capsys.readouterr().out


def test_run_steps_first_no_continue(isc):
    """First step does not use --continue."""
    mock_streaming, _ = _run_steps_with_ok_mock(isc)
    assert "--continue" not in mock_streaming.call_args_list[0][0][0]


def test_run_steps_second_uses_continue(isc):
    """Second step uses --continue."""
    mock_streaming, _ = _run_steps_with_ok_mock(isc)
    assert "--continue" in mock_streaming.call_args_list[1][0][0]


# ---- run_steps content filter retry -----------------------------------------


def test_run_steps_retries_on_content_filter(isc):
    """run_steps retries a step when ContentFilterError is raised."""
    steps = [("Step A", "do something")]
    mock_streaming = MagicMock(
        side_effect=[ContentFilterError("blocked"), "ok"],
    )
    with patch("implement_subclause.run_claude_streaming", mock_streaming):
        result = isc.run_steps(steps, model="opus")
    assert result == ["ok"]


def test_run_steps_retry_uses_continue(isc):
    """Retry attempt uses --continue flag."""
    steps = [("Step A", "do something")]
    mock_streaming = MagicMock(
        side_effect=[ContentFilterError("blocked"), "ok"],
    )
    with patch("implement_subclause.run_claude_streaming", mock_streaming):
        isc.run_steps(steps, model="opus")
    retry_cmd = mock_streaming.call_args_list[1][0][0]
    assert "--continue" in retry_cmd


def test_run_steps_retry_uses_retry_prompt(isc):
    """Retry attempt uses the content filter retry prompt."""
    steps = [("Step A", "do something")]
    mock_streaming = MagicMock(
        side_effect=[ContentFilterError("blocked"), "ok"],
    )
    with patch("implement_subclause.run_claude_streaming", mock_streaming):
        isc.run_steps(steps, model="opus")
    retry_prompt = mock_streaming.call_args_list[1][0][1]
    assert "content filter" in retry_prompt.lower()


def test_run_steps_exits_after_max_retries(isc):
    """run_steps exits when all retry attempts are exhausted."""
    steps = [("Step A", "do something")]
    mock_streaming = MagicMock(side_effect=ContentFilterError("blocked"))
    with (
        patch("implement_subclause.run_claude_streaming", mock_streaming),
        pytest.raises(SystemExit),
    ):
        isc.run_steps(steps, model="opus")


def test_run_steps_does_not_retry_other_errors(isc):
    """run_steps does not retry on non-ContentFilterError exceptions."""
    steps = [("Step A", "do something")]
    mock_streaming = MagicMock(side_effect=SystemExit(1))
    with (
        patch("implement_subclause.run_claude_streaming", mock_streaming),
        pytest.raises(SystemExit),
    ):
        isc.run_steps(steps, model="opus")
    assert mock_streaming.call_count == 1
