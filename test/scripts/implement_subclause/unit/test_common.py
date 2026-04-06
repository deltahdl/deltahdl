"""Unit tests for implement_subclause."""

from unittest.mock import MagicMock, patch

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


def test_build_steps_has_12_steps(isc):
    """build_steps returns exactly 12 steps."""
    assert len(isc.build_steps("4.1", "~/LRM.txt")) == 12


def test_build_steps_first_mentions_lrm(isc):
    """First step prompt mentions the LRM."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "LRM" in steps[0][1]


def test_build_steps_last_mentions_summarize(isc):
    """Last step prompt asks for a summary."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "Summarize" in steps[-1][1]


def test_build_steps_summary_requires_self_contained(isc):
    """Summary step requires a self-contained list, not a back-reference."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "self-contained" in steps[-1][1]


def test_build_steps_second_checks_implementability(isc):
    """Second step asks Claude if the subclause is implementable."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "IMPLEMENTABLE" in steps[1][1]


def test_build_steps_implementability_mentions_concrete_statements(isc):
    """Implementability step recognizes subclauses with concrete statements."""
    steps = isc.build_steps("6.20", "~/LRM.txt", exclude="6.20.1")
    assert "concrete statements" in steps[1][1]


def test_build_steps_implementability_mentions_definitional_claims(isc):
    """Implementability step recognizes definitional claims as implementable."""
    steps = isc.build_steps("6.2", "~/LRM.txt")
    assert "definitional claims" in steps[1][1]


def test_build_steps_implementability_requires_rationale(isc):
    """Implementability step requires a RATIONALE: line in the response."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "RATIONALE:" in steps[1][1]


def test_build_steps_implementability_specifies_format(isc):
    """Implementability step pins the exact response format."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    prompt = steps[1][1]
    # The prompt must require both fields, in order, in a fixed format.
    assert "IMPLEMENTABLE:" in prompt
    assert prompt.index("RATIONALE:") < prompt.index("IMPLEMENTABLE:")


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


_OK_STDOUT = '{"result": "- Done because needed"}'
_OK_STEP2_STDOUT = (
    '{"result": "RATIONALE: §X.Y defines concrete syntax and semantics.'
    '\\nIMPLEMENTABLE: yes"}'
)


def _mock_run_ok():
    """Return a MagicMock for run_claude_cli that always succeeds."""
    return MagicMock(
        return_value=MagicMock(returncode=0, stdout=_OK_STDOUT, stderr=""),
    )


def _make_ok_side_effect():
    """Return a fake run_with_dots that satisfies the step 2 parser."""
    state = {"count": 0}

    def fake(_func, *_args, **_kwargs):
        state["count"] += 1
        if state["count"] == 2:
            return MagicMock(
                returncode=0, stdout=_OK_STEP2_STDOUT, stderr="",
            )
        return MagicMock(returncode=0, stdout=_OK_STDOUT, stderr="")

    return fake


def _run_steps_and_capture(isc):
    """Build steps, mock run_with_dots, run, return mock."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    mock_rwd = MagicMock(side_effect=_make_ok_side_effect())
    with patch("implement_subclause.run_with_dots", mock_rwd):
        isc.run_steps(steps, model="opus")
    return mock_rwd


def test_run_steps_call_count(isc):
    """run_steps calls run_with_dots 12 times (once per step)."""
    assert _run_steps_and_capture(isc).call_count == 12


def _mock_claude_cli_with_step2():
    """Return a run_claude_cli mock that returns a valid step 2 response."""
    state = {"count": 0}

    def fake(*_args, **_kwargs):
        state["count"] += 1
        stdout = _OK_STEP2_STDOUT if state["count"] == 2 else _OK_STDOUT
        return MagicMock(returncode=0, stdout=stdout, stderr="")

    return MagicMock(side_effect=fake)


def test_run_steps_returns_summary(isc):
    """run_steps returns the result text from the last step."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_claude_cli",
               _mock_claude_cli_with_step2()), \
         patch("implement_subclause.run_with_dots",
               side_effect=lambda f, *a, **kw: f(*a, **kw)):
        result = isc.run_steps(steps, model="opus")
    assert result == "- Done because needed"


def test_run_steps_prints_step_numbers(isc, capsys):
    """run_steps prints step numbers in stdout."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_claude_cli",
               _mock_claude_cli_with_step2()), \
         patch("implement_subclause.run_with_dots",
               side_effect=lambda f, *a, **kw: f(*a, **kw)):
        isc.run_steps(steps, model="opus")
    out = capsys.readouterr().out
    assert "Step 1/12:" in out


_NOT_IMPL_RATIONALE = (
    "Section enumerates only block contexts already covered in §9 and adds"
    " no new behavior."
)
_NOT_IMPL_STDOUT = (
    '{"result": "RATIONALE: ' + _NOT_IMPL_RATIONALE
    + '\\nIMPLEMENTABLE: no"}'
)


def _run_not_implementable(isc):
    """Run steps with a not-implementable verdict, return (result, count)."""
    not_impl = MagicMock(
        returncode=0, stdout=_NOT_IMPL_STDOUT, stderr="",
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


def test_run_steps_returns_not_implementable_sentinel(isc):
    """run_steps returns a NotImplementable sentinel for not-implementable."""
    result, _ = _run_not_implementable(isc)
    assert isinstance(result, isc.NotImplementable)


def test_run_steps_captures_rationale_on_not_implementable(isc):
    """The NotImplementable sentinel carries the rationale text."""
    result, _ = _run_not_implementable(isc)
    assert result.rationale == _NOT_IMPL_RATIONALE


def test_run_steps_implementable_yes_does_not_skip(isc):
    """A 'yes' response with rationale runs all 12 steps and returns summary."""
    yes_stdout = (
        '{"result": "RATIONALE: Defines concrete syntax X and semantics Y.'
        '\\nIMPLEMENTABLE: yes"}'
    )

    def fake_run(_func, *_args, **_kwargs):
        fake_run.count += 1
        if fake_run.count == 2:
            return MagicMock(returncode=0, stdout=yes_stdout, stderr="")
        return MagicMock(returncode=0, stdout=_OK_STDOUT, stderr="")

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        result = isc.run_steps(steps, model="opus")
    assert fake_run.count == 12
    assert result == "- Done because needed"


@patch("implement_subclause.sys.exit")
def test_run_steps_exits_on_malformed_step2(mock_exit, isc):
    """A step 2 response missing RATIONALE: causes a hard failure."""
    malformed = '{"result": "IMPLEMENTABLE: no"}'

    def fake_run(_func, *_args, **_kwargs):
        fake_run.count += 1
        if fake_run.count == 2:
            return MagicMock(returncode=0, stdout=malformed, stderr="")
        return MagicMock(returncode=0, stdout=_OK_STDOUT, stderr="")

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        isc.run_steps(steps, model="opus")
    assert mock_exit.called


@patch("implement_subclause.sys.exit")
def test_run_steps_exits_on_empty_rationale(mock_exit, isc):
    """A step 2 response with an empty RATIONALE causes a hard failure."""
    empty = '{"result": "RATIONALE:\\nIMPLEMENTABLE: no"}'

    def fake_run(_func, *_args, **_kwargs):
        fake_run.count += 1
        if fake_run.count == 2:
            return MagicMock(returncode=0, stdout=empty, stderr="")
        return MagicMock(returncode=0, stdout=_OK_STDOUT, stderr="")

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        isc.run_steps(steps, model="opus")
    assert mock_exit.called


# ---- _parse_implementability ------------------------------------------------


def test_parse_implementability_yes(isc):
    """_parse_implementability returns ('yes', rationale) for a yes verdict."""
    parse = getattr(isc, "_parse_implementability")
    stdout = (
        '{"result": "RATIONALE: defines syntax X.\\nIMPLEMENTABLE: yes"}'
    )
    assert parse(stdout) == ("yes", "defines syntax X.")


def test_parse_implementability_no(isc):
    """_parse_implementability returns ('no', rationale) for a no verdict."""
    parse = getattr(isc, "_parse_implementability")
    stdout = (
        '{"result": "RATIONALE: just a chapter intro.\\nIMPLEMENTABLE: no"}'
    )
    assert parse(stdout) == ("no", "just a chapter intro.")


def test_parse_implementability_handles_plain_text(isc):
    """_parse_implementability works on raw (non-JSON) stdout."""
    parse = getattr(isc, "_parse_implementability")
    stdout = "RATIONALE: foo\nIMPLEMENTABLE: yes"
    assert parse(stdout) == ("yes", "foo")


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



def test_run_steps_first_no_continue(isc):
    """First step does not use --continue."""
    mock_rwd = _run_steps_and_capture(isc)
    assert "--continue" not in mock_rwd.call_args_list[0][0][1]


def test_run_steps_second_uses_continue(isc):
    """Second step uses --continue."""
    mock_rwd = _run_steps_and_capture(isc)
    assert "--continue" in mock_rwd.call_args_list[1][0][1]
