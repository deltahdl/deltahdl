"""Unit tests for implement_subclause."""

import json
from unittest.mock import MagicMock, patch

from lib.python.classify import build_hierarchy

from .conftest import step2_envelope as _step2_envelope


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


def test_build_steps_has_10_steps(isc):
    """build_steps returns exactly 10 steps after merge and summary removal."""
    assert len(isc.build_steps("4.1", "~/LRM.txt")) == 10


def test_build_steps_first_mentions_lrm(isc):
    """First step prompt embeds the LRM read instruction."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "LRM" in steps[0][1]


def test_build_steps_last_is_audit_scope(isc):
    """Last step is the model self-audit (Auditing scope)."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert steps[-1][0] == "Auditing scope"


def test_build_steps_second_checks_implementability(isc):
    """Second step asks Claude to enumerate implementability evidence."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "evidence" in steps[0][1]


def test_build_steps_implementability_taxonomy_free_examples(isc):
    """Implementability prompt names cross-spec evidence examples."""
    steps = isc.build_steps("6.20", "~/LRM.txt", exclude="6.20.1")
    assert "RFC 2119" in steps[0][1]


def test_build_steps_implementability_warns_against_definitional(isc):
    """Implementability prompt warns against dismissing definitions."""
    steps = isc.build_steps("6.2", "~/LRM.txt")
    assert "definitional" in steps[0][1]


def test_build_steps_implementability_requests_rationale_field(isc):
    """Implementability prompt asks for a 'rationale' field in the JSON."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "rationale" in steps[0][1]


def test_build_steps_implementability_requests_verdict_field(isc):
    """Implementability prompt asks for a 'verdict' field in the JSON."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "verdict" in steps[0][1]


def test_build_steps_implementability_states_override_rule(isc):
    """Prompt states the 'evidence non-empty → verdict yes' rule."""
    prompt = isc.build_steps("4.1", "~/LRM.txt")[0][1]
    assert "non-empty" in prompt


def test_build_steps_each_has_description(isc):
    """Each step has a non-empty description."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert all(desc for desc, _ in steps)


def test_build_steps_delete_step_scoped_to_subclause(isc):
    """Delete duplicates step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[3][1]


def test_build_steps_rename_suites_scoped_to_subclause(isc):
    """Rename suites step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[5][1]


def test_build_steps_rename_tests_scoped_to_subclause(isc):
    """Rename tests step references the subclause."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    assert "§4.1" in steps[6][1]


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
_OK_STEP2_EVIDENCE = [
    {"quote": "X shall Y", "why_testable": "parser must enforce X→Y"},
]
_OK_STEP2_STDOUT = _step2_envelope(
    "yes", evidence=_OK_STEP2_EVIDENCE, rationale="defines concrete syntax",
)


def _mock_run_ok():
    """Return a MagicMock for run_claude_cli that always succeeds."""
    return MagicMock(
        return_value=MagicMock(returncode=0, stdout=_OK_STDOUT, stderr=""),
    )


def _make_ok_side_effect():
    """Return a fake run_with_dots that satisfies the step 1 parser."""
    state = {"count": 0}

    def fake(_func, *_args, **_kwargs):
        state["count"] += 1
        if state["count"] == 1:
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
    """run_steps calls run_with_dots 10 times (once per step)."""
    assert _run_steps_and_capture(isc).call_count == 10


def _mock_claude_cli_with_step2():
    """Return a run_claude_cli mock that returns a valid step 1 response."""
    state = {"count": 0}

    def fake(*_args, **_kwargs):
        state["count"] += 1
        stdout = _OK_STEP2_STDOUT if state["count"] == 1 else _OK_STDOUT
        return MagicMock(returncode=0, stdout=stdout, stderr="")

    return MagicMock(side_effect=fake)


def test_run_steps_returns_none_on_success(isc):
    """run_steps returns None after a successful run of all steps."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_claude_cli",
               _mock_claude_cli_with_step2()), \
         patch("implement_subclause.run_with_dots",
               side_effect=lambda f, *a, **kw: f(*a, **kw)):
        result = isc.run_steps(steps, model="opus")
    assert result is None


def test_run_steps_prints_step_numbers(isc, capsys):
    """run_steps prints step numbers in stdout."""
    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_claude_cli",
               _mock_claude_cli_with_step2()), \
         patch("implement_subclause.run_with_dots",
               side_effect=lambda f, *a, **kw: f(*a, **kw)):
        isc.run_steps(steps, model="opus")
    out = capsys.readouterr().out
    assert "Step 1/10:" in out


_NOT_IMPL_RATIONALE = (
    "Section enumerates only block contexts already covered in §9 and adds"
    " no new behavior."
)
_NOT_IMPL_STDOUT = _step2_envelope(
    "no", evidence=[], rationale=_NOT_IMPL_RATIONALE,
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
        """Return not-implementable for step 1, summary for last."""
        fake_run.count += 1
        if fake_run.count == 1:
            return not_impl
        return summary_result

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        result = isc.run_steps(steps, model="opus")
    return result, fake_run.count


def test_run_steps_returns_immediately_when_not_implementable(isc):
    """run_steps stops after step 1 when the subclause is not implementable."""
    _, count = _run_not_implementable(isc)
    assert count == 1


def test_run_steps_returns_not_implementable_sentinel(isc):
    """run_steps returns a NotImplementable sentinel for not-implementable."""
    result, _ = _run_not_implementable(isc)
    assert isinstance(result, isc.NotImplementable)


def test_run_steps_captures_rationale_on_not_implementable(isc):
    """The NotImplementable sentinel carries the rationale text."""
    result, _ = _run_not_implementable(isc)
    assert result.rationale == _NOT_IMPL_RATIONALE


_YES_STEP2_STDOUT = _step2_envelope(
    "yes",
    evidence=[{"quote": "Defines syntax X.", "why_testable": "parser must accept X"}],
    rationale="Defines concrete syntax X and semantics Y.",
)


def _run_implementable_yes(isc):
    """Run all steps with a yes verdict on step 1; return (result, count)."""
    def fake_run(_func, *_args, **_kwargs):
        fake_run.count += 1
        if fake_run.count == 1:
            return MagicMock(
                returncode=0, stdout=_YES_STEP2_STDOUT, stderr="",
            )
        return MagicMock(returncode=0, stdout=_OK_STDOUT, stderr="")

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        result = isc.run_steps(steps, model="opus")
    return result, fake_run.count


def test_run_steps_implementable_yes_runs_all_steps(isc):
    """A 'yes' response with rationale runs all 10 steps."""
    _, count = _run_implementable_yes(isc)
    assert count == 10


def test_run_steps_implementable_yes_returns_none(isc):
    """A 'yes' response causes run_steps to return None on success."""
    result, _ = _run_implementable_yes(isc)
    assert result is None


def _run_steps_with_step2_stdout(isc, step2_stdout):
    """Run steps where step 1 returns ``step2_stdout``."""
    def fake_run(_func, *_args, **_kwargs):
        fake_run.count += 1
        if fake_run.count == 1:
            return MagicMock(returncode=0, stdout=step2_stdout, stderr="")
        return MagicMock(returncode=0, stdout=_OK_STDOUT, stderr="")

    fake_run.count = 0

    steps = isc.build_steps("4.1", "~/LRM.txt")
    with patch("implement_subclause.run_with_dots", side_effect=fake_run):
        isc.run_steps(steps, model="opus")


@patch("implement_subclause.sys.exit")
def test_run_steps_exits_on_malformed_step2(mock_exit, isc):
    """A step 2 response with a missing key causes a hard failure."""
    bad = json.dumps({"result": json.dumps({"verdict": "no"})})
    _run_steps_with_step2_stdout(isc, bad)
    assert mock_exit.called


@patch("implement_subclause.sys.exit")
def test_run_steps_exits_on_empty_rationale(mock_exit, isc):
    """A step 2 response with an empty rationale causes a hard failure."""
    bad = _step2_envelope("no", evidence=[], rationale="   ")
    _run_steps_with_step2_stdout(isc, bad)
    assert mock_exit.called


# ---- _parse_implementability (legacy slim coverage) ------------------------


def test_parse_implementability_returns_three_tuple(isc):
    """_parse_implementability returns a (verdict, rationale, evidence) tuple."""
    parse = getattr(isc, "_parse_implementability")
    result = parse(_step2_envelope("yes", rationale="defines syntax X."))
    assert len(result) == 3


def test_parse_implementability_handles_raw_payload(isc):
    """_parse_implementability accepts a payload with no result envelope."""
    parse = getattr(isc, "_parse_implementability")
    payload = json.dumps({
        "evidence": [], "verdict": "no", "rationale": "intro only.",
    })
    verdict, _rationale, _evidence = parse(payload)
    assert verdict == "no"


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
