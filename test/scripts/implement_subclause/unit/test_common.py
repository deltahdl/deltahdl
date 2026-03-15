"""Unit tests for implement_subclause."""

from unittest.mock import MagicMock, patch

from lib.python.classify import build_hierarchy


# ---- build_hierarchy --------------------------------------------------------


class TestBuildHierarchyNumeric:
    """Tests for numeric (non-annex) clauses."""

    def test_depth_1(self, isc):
        """Clause '4' produces depth-1 numeric hierarchy."""
        assert build_hierarchy("4") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4",
        }

    def test_depth_2(self, isc):
        """Clause '4.1' produces depth-2 numeric hierarchy."""
        assert build_hierarchy("4.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": [],
            "subclause": "4.1",
        }

    def test_depth_3(self, isc):
        """Clause '6.24.1' produces depth-3 numeric hierarchy."""
        assert build_hierarchy("6.24.1") == {
            "is_annex": False,
            "clause_number": "6",
            "ancestors": ["6.24"],
            "subclause": "6.24.1",
        }

    def test_depth_4(self, isc):
        """Clause '4.4.3.1' produces depth-4 numeric hierarchy."""
        assert build_hierarchy("4.4.3.1") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": ["4.4", "4.4.3"],
            "subclause": "4.4.3.1",
        }

    def test_depth_5(self, isc):
        """Clause '4.4.3.1.2' produces depth-5 numeric hierarchy."""
        assert build_hierarchy("4.4.3.1.2") == {
            "is_annex": False,
            "clause_number": "4",
            "ancestors": ["4.4", "4.4.3", "4.4.3.1"],
            "subclause": "4.4.3.1.2",
        }


class TestBuildHierarchyAnnex:
    """Tests for annex (uppercase letter) clauses."""

    def test_depth_1(self, isc):
        """Clause 'B' produces depth-1 annex hierarchy."""
        assert build_hierarchy("B") == {
            "is_annex": True,
            "collection": "Annex B",
            "letter": "B",
            "ancestors": [],
            "subclause": "B",
        }

    def test_depth_2(self, isc):
        """Clause 'A.8' produces depth-2 annex hierarchy."""
        assert build_hierarchy("A.8") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": [],
            "subclause": "A.8",
        }

    def test_depth_3(self, isc):
        """Clause 'A.8.1' produces depth-3 annex hierarchy."""
        assert build_hierarchy("A.8.1") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.8"],
            "subclause": "A.8.1",
        }

    def test_depth_4(self, isc):
        """Clause 'A.7.5.3' produces depth-4 annex hierarchy."""
        assert build_hierarchy("A.7.5.3") == {
            "is_annex": True,
            "collection": "Annex A",
            "letter": "A",
            "ancestors": ["A.7", "A.7.5"],
            "subclause": "A.7.5.3",
        }

    def test_depth_5(self, isc):
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


def test_build_steps_has_11_steps(isc):
    """build_steps returns exactly 11 steps."""
    assert len(isc.build_steps("4.1", "~/LRM.txt")) == 11


def test_build_steps_first_mentions_lrm(isc):
    """First step prompt mentions the LRM."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "LRM" in steps[0][1]


def test_build_steps_last_mentions_action_summary(isc):
    """Last step prompt mentions ACTION_SUMMARY."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "ACTION_SUMMARY" in steps[-1][1]


def test_build_steps_second_checks_implementability(isc):
    """Second step asks Claude if the subclause is implementable."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "IMPLEMENTABLE" in steps[1][1]


def test_build_steps_each_has_description(isc):
    """Each step has a non-empty description."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert all(desc for desc, _ in steps)


def test_build_steps_delete_step_scoped_to_subclause(isc):
    """Delete duplicates step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[4][1]


def test_build_steps_rename_suites_scoped_to_subclause(isc):
    """Rename suites step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[6][1]


def test_build_steps_rename_tests_scoped_to_subclause(isc):
    """Rename tests step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[7][1]


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


# ---- run_steps -------------------------------------------------------------


_OK_STDOUT = (
    'ACTION_SUMMARY_START\n- Done because needed\nACTION_SUMMARY_END'
)


def _mock_run_ok():
    """Return a MagicMock for run_claude_cli that always succeeds."""
    return MagicMock(
        return_value=MagicMock(returncode=0, stdout=_OK_STDOUT, stderr=""),
    )


def _run_steps_and_capture(isc):
    """Build steps, mock run_with_dots, run, return mock."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    mock_rwd = MagicMock(
        return_value=MagicMock(returncode=0, stdout=_OK_STDOUT, stderr=""),
    )
    with patch("implement_subclause.run_with_dots", mock_rwd):
        isc.run_steps(steps, model="opus")
    return mock_rwd


def test_run_steps_call_count(isc):
    """run_steps calls run_with_dots 11 times (once per step)."""
    assert _run_steps_and_capture(isc).call_count == 11


def test_run_steps_returns_action_summary(isc):
    """run_steps returns the ACTION_SUMMARY from the last step."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_claude_cli", _mock_run_ok()), \
         patch("implement_subclause.run_with_dots",
               side_effect=lambda f, *a, **kw: f(*a, **kw)):
        result = isc.run_steps(steps, model="opus")
    assert result == "- Done because needed"


def test_run_steps_prints_step_numbers(isc, capsys):
    """run_steps prints step numbers in stdout."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_claude_cli", _mock_run_ok()), \
         patch("implement_subclause.run_with_dots",
               side_effect=lambda f, *a, **kw: f(*a, **kw)):
        isc.run_steps(steps, model="opus")
    out = capsys.readouterr().out
    assert "Step 1/11:" in out


def _run_not_implementable(isc):
    """Run steps with a not-implementable verdict, return (result, count)."""
    not_impl = MagicMock(
        returncode=0, stdout="IMPLEMENTABLE: no", stderr="",
    )
    summary_result = MagicMock(
        returncode=0, stdout=_OK_STDOUT, stderr="",
    )

    def fake_run(_func, *_args, **_kwargs):
        """Return not-implementable for step 2, summary for last."""
        fake_run.count += 1
        if fake_run.count == 2:
            return not_impl
        return summary_result

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        result = isc.run_steps(steps, model="opus")
    return result, fake_run.count


def test_run_steps_skips_when_not_implementable(isc):
    """run_steps skips implementation steps when subclause is not implementable."""
    _, count = _run_not_implementable(isc)
    assert count == 3  # read, check, summary


def test_run_steps_returns_none_when_not_implementable(isc):
    """run_steps returns None when subclause is not implementable."""
    result, _ = _run_not_implementable(isc)
    assert result is None


@patch("implement_subclause.sys.exit")
def test_run_steps_exits_on_failure(mock_exit, isc):
    """run_steps exits when a step fails."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    fail = MagicMock(
        return_value=MagicMock(returncode=1, stdout="", stderr="err"),
    )
    with patch("implement_subclause.run_with_dots", fail):
        isc.run_steps(steps, model="opus")
    assert mock_exit.called


@patch("implement_subclause.sys.exit")
def test_run_steps_exits_on_missing_summary(mock_exit, isc):
    """run_steps exits when the last step has no ACTION_SUMMARY."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    no_summary = MagicMock(
        return_value=MagicMock(returncode=0, stdout='{"result":"done"}', stderr=""),
    )
    with patch("implement_subclause.run_with_dots", no_summary):
        isc.run_steps(steps, model="opus")
    assert mock_exit.called


def test_run_steps_first_no_continue(isc):
    """First step does not use --continue."""
    mock_rwd = _run_steps_and_capture(isc)
    assert "--continue" not in mock_rwd.call_args_list[0][0][1]


def test_run_steps_second_uses_continue(isc):
    """Second step uses --continue."""
    mock_rwd = _run_steps_and_capture(isc)
    assert "--continue" in mock_rwd.call_args_list[1][0][1]
