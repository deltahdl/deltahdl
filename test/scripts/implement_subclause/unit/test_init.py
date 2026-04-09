"""Unit tests for implement_subclause (arg parsing and dispatch)."""

import json
import runpy
from unittest.mock import MagicMock, patch

import pytest

from .conftest import step2_envelope as _step2_envelope_helper


# ---- clause_depth -----------------------------------------------------------


def test_clause_depth_1(isc):
    """Single component has depth 1."""
    assert isc.clause_depth("4") == 1


def test_clause_depth_1_annex(isc):
    """Single letter component has depth 1."""
    assert isc.clause_depth("B") == 1


def test_clause_depth_2(isc):
    """Two components have depth 2."""
    assert isc.clause_depth("4.1") == 2


def test_clause_depth_3(isc):
    """Three components have depth 3."""
    assert isc.clause_depth("6.24.1") == 3


def test_clause_depth_4(isc):
    """Four components have depth 4."""
    assert isc.clause_depth("4.4.3.1") == 4


def test_clause_depth_5(isc):
    """Five components have depth 5."""
    assert isc.clause_depth("4.4.3.1.2") == 5


# ---- parse_args -------------------------------------------------------------


def test_parse_args_requires_issue(isc, tmp_path):
    """--issue is required; omitting it exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args(["--lrm", str(lrm), "--subclause", "4.1"])


def test_parse_args_accepts_issue(isc, tmp_path):
    """--issue is parsed as int."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args(["--lrm", str(lrm), "--subclause", "4.1", "--issue", "8"])
    assert args.issue == 8


def test_parse_args_model_default(isc, tmp_path):
    """--model defaults to 'opus'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.model == "opus"


def test_parse_args_model_override(isc, tmp_path):
    """--model can be overridden."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--model", "opus",
    ])
    assert args.model == "opus"


def test_parse_args_rejects_bad_clause(isc, tmp_path):
    """Invalid clause format exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(lrm), "--subclause", "bad", "--issue", "8",
        ])


def test_parse_args_rejects_missing_lrm(isc, tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--subclause", "4.1",
            "--issue", "8",
        ])


def test_parse_args_accepts_annex_clause(isc, tmp_path):
    """Uppercase letter clause is accepted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "B", "--issue", "44",
    ])
    assert (args.subclause, args.issue) == ("B", 44)


def test_parse_args_continue_flag(isc, tmp_path):
    """--continue sets continue_session to True."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--continue",
    ])
    assert args.continue_session is True


def test_parse_args_continue_default_false(isc, tmp_path):
    """continue_session defaults to False."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.continue_session is False


def test_parse_args_exclude_default_empty(isc, tmp_path):
    """--exclude defaults to empty string."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.exclude == ""


def test_parse_args_exclude_value(isc, tmp_path):
    """--exclude accepts a comma-separated string."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "15.3", "--issue", "8",
        "--exclude", "15.3.1,15.3.2",
    ])
    assert args.exclude == "15.3.1,15.3.2"


# ---- build_action_summary --------------------------------------------------


def test_build_action_summary_added_bullets(isc):
    """Added paths produce 'Added' bullets in sorted order."""
    summary = isc.build_action_summary(["b.cpp", "a.cpp"], [], [])
    assert summary == "- Added a.cpp\n- Added b.cpp"


def test_build_action_summary_modified_bullets(isc):
    """Modified paths produce 'Modified' bullets."""
    summary = isc.build_action_summary([], ["x.h"], [])
    assert summary == "- Modified x.h"


def test_build_action_summary_deleted_bullets(isc):
    """Deleted paths produce 'Deleted' bullets."""
    summary = isc.build_action_summary([], [], ["old.cpp"])
    assert summary == "- Deleted old.cpp"


def test_build_action_summary_combined(isc):
    """Combined output orders added, then modified, then deleted."""
    summary = isc.build_action_summary(["a.cpp"], ["b.h"], ["c.cpp"])
    assert summary == "- Added a.cpp\n- Modified b.h\n- Deleted c.cpp"


def test_build_action_summary_empty(isc):
    """Empty inputs produce an empty string."""
    assert isc.build_action_summary([], [], []) == ""


# ---- main ------------------------------------------------------------------


def _run_main_success(isc, tmp_path, *, changes=(["foo.cpp"], [], [])):
    """Run main() with run_steps success and stubbed git changes."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with (
        patch("implement_subclause.run_steps",
              return_value=None) as mock_run,
        patch("implement_subclause.commit_implementation") as mock_commit,
        patch("implement_subclause.get_porcelain_changes",
              return_value=changes),
    ):
        isc.main([
            "--lrm", str(lrm), "--subclause", "6.6.1",
            "--issue", "8", "--model", "opus",
        ])
    return {"run": mock_run, "commit": mock_commit}


def test_main_dispatches_depth_1(isc, tmp_path):
    """main() passes model to run_steps."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with (
        patch("implement_subclause.run_steps",
              return_value=None) as mock_run,
        patch("implement_subclause.commit_implementation"),
        patch("implement_subclause.get_porcelain_changes",
              return_value=([], [], [])),
    ):
        isc.main([
            "--lrm", str(lrm), "--subclause", "4",
            "--issue", "6", "--model", "opus",
        ])
    assert mock_run.call_args[1]["model"] == "opus"


def test_main_calls_commit_implementation_subclause(isc, tmp_path):
    """main() calls commit_implementation with the subclause."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[0][0] == "6.6.1"


def test_main_calls_commit_implementation_issue(isc, tmp_path):
    """main() calls commit_implementation with the issue number."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[0][1] == 8


def test_main_passes_action_to_commit(isc, tmp_path):
    """main() builds the action summary from git status and passes it down."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[1]["action"] == "- Added foo.cpp"


def test_main_prints_action_summary(isc, tmp_path, capsys):
    """main() prints the action summary to stdout."""
    _run_main_success(isc, tmp_path)
    assert "- Added foo.cpp" in capsys.readouterr().out



_NOT_IMPL_FIXTURE_RATIONALE = (
    "Section §6.6.1 only points at §6.6.2 for actual semantics."
)


def _run_main_not_implementable(isc, tmp_path):
    """Run main() with a NotImplementable sentinel; return mocks dict."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    sentinel = isc.NotImplementable(rationale=_NOT_IMPL_FIXTURE_RATIONALE)
    with (
        patch("implement_subclause.subprocess.run",
              return_value=MagicMock(returncode=0)) as mock_gh,
        patch("implement_subclause.commit_implementation") as mock_commit,
        patch("implement_subclause.run_steps", return_value=sentinel),
    ):
        isc.main(["--lrm", str(lrm), "--subclause", "6.6.1",
                  "--issue", "8", "--model", "opus"])
    return {"gh": mock_gh, "commit": mock_commit}


def test_main_closes_issue_when_not_implementable(isc, tmp_path):
    """main() closes issue with comment when not implementable."""
    mocks = _run_main_not_implementable(isc, tmp_path)
    assert "close" in mocks["gh"].call_args[0][0]


def test_main_close_comment_deemed_not_implementable(isc, tmp_path):
    """main() comment contains the 'Deemed not implementable.' header."""
    mocks = _run_main_not_implementable(isc, tmp_path)
    cmd = mocks["gh"].call_args[0][0]
    comment = cmd[cmd.index("--comment") + 1]
    assert "Deemed not implementable." in comment


def test_main_close_comment_includes_rationale(isc, tmp_path):
    """main() embeds the captured rationale in the close comment."""
    mocks = _run_main_not_implementable(isc, tmp_path)
    cmd = mocks["gh"].call_args[0][0]
    comment = cmd[cmd.index("--comment") + 1]
    assert _NOT_IMPL_FIXTURE_RATIONALE in comment


def test_main_close_comment_labels_rationale(isc, tmp_path):
    """main() prefixes the rationale block with a 'Rationale:' label."""
    mocks = _run_main_not_implementable(isc, tmp_path)
    cmd = mocks["gh"].call_args[0][0]
    comment = cmd[cmd.index("--comment") + 1]
    assert "Rationale:" in comment


def test_main_skips_commit_when_not_implementable(isc, tmp_path):
    """main() does not call commit_implementation when not implementable."""
    mocks = _run_main_not_implementable(isc, tmp_path)
    assert not mocks["commit"].called


# ---- _parse_implementability (evidence-based JSON envelope) ----------------


def _make_step2_response(evidence=None, verdict="yes",
                         rationale="reasonable rationale here"):
    """Build a Claude CLI envelope wrapping a Step 2 JSON response."""
    return _step2_envelope_helper(
        verdict, evidence=evidence, rationale=rationale,
    )


_EVIDENCE_FIXTURE = [
    {"quote": "X shall Y", "why_testable": "parser must enforce X→Y"},
]


def test_parse_implementability_yes_verdict_passes_through(isc):
    """Yes verdict with evidence stays yes."""
    parse = getattr(isc, "_parse_implementability")
    response = _make_step2_response(evidence=_EVIDENCE_FIXTURE, verdict="yes")
    verdict, _rationale, _evidence = parse(response)
    assert verdict == "yes"


def test_parse_implementability_no_verdict_no_evidence_stays_no(isc):
    """No verdict with empty evidence stays no."""
    parse = getattr(isc, "_parse_implementability")
    response = _make_step2_response(evidence=[], verdict="no")
    verdict, _rationale, _evidence = parse(response)
    assert verdict == "no"


def test_parse_implementability_override_no_to_yes(isc):
    """No verdict with non-empty evidence is overridden to yes."""
    parse = getattr(isc, "_parse_implementability")
    response = _make_step2_response(evidence=_EVIDENCE_FIXTURE, verdict="no")
    verdict, _rationale, _evidence = parse(response)
    assert verdict == "yes"


def test_parse_implementability_override_annotates_rationale(isc):
    """Overridden rationale carries an OVERRIDE marker."""
    parse = getattr(isc, "_parse_implementability")
    response = _make_step2_response(
        evidence=_EVIDENCE_FIXTURE, verdict="no",
        rationale="text says it's just an overview",
    )
    _verdict, rationale, _evidence = parse(response)
    assert "OVERRIDE" in rationale


def test_parse_implementability_override_preserves_original_rationale(isc):
    """Overridden rationale embeds the model's original rationale."""
    parse = getattr(isc, "_parse_implementability")
    response = _make_step2_response(
        evidence=_EVIDENCE_FIXTURE, verdict="no",
        rationale="text says it's just an overview",
    )
    _verdict, rationale, _evidence = parse(response)
    assert "text says it's just an overview" in rationale


def test_parse_implementability_returns_evidence_list(isc):
    """Parser returns the evidence list verbatim."""
    parse = getattr(isc, "_parse_implementability")
    items = [
        {"quote": "Q1", "why_testable": "W1"},
        {"quote": "Q2", "why_testable": "W2"},
    ]
    response = _make_step2_response(evidence=items, verdict="no")
    _verdict, _rationale, evidence = parse(response)
    assert evidence == items


def test_parse_implementability_yes_verdict_no_evidence_accepted(isc):
    """Yes verdict with empty evidence is accepted (false positive recoverable)."""
    parse = getattr(isc, "_parse_implementability")
    response = _make_step2_response(evidence=[], verdict="yes")
    verdict, _rationale, _evidence = parse(response)
    assert verdict == "yes"


def test_parse_implementability_strips_markdown_fence(isc):
    """Parser strips ```json fences before parsing."""
    parse = getattr(isc, "_parse_implementability")
    payload = json.dumps({
        "evidence": [], "verdict": "no", "rationale": "overview only.",
    })
    fenced = f"```json\n{payload}\n```"
    response = json.dumps({"result": fenced})
    verdict, _rationale, _evidence = parse(response)
    assert verdict == "no"


def _step2_envelope(payload):
    """Wrap a payload object in the Claude CLI result envelope."""
    return json.dumps({"result": json.dumps(payload)})


def test_parse_implementability_raises_on_missing_evidence_key(isc):
    """Missing evidence key raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({"verdict": "no", "rationale": "x"})
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_missing_verdict_key(isc):
    """Missing verdict key raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({"evidence": [], "rationale": "x"})
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_missing_rationale_key(isc):
    """Missing rationale key raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({"evidence": [], "verdict": "no"})
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_evidence_item_missing_quote(isc):
    """Evidence item missing 'quote' raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({
        "evidence": [{"why_testable": "W"}],
        "verdict": "yes",
        "rationale": "r",
    })
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_evidence_item_missing_why(isc):
    """Evidence item missing 'why_testable' raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({
        "evidence": [{"quote": "Q"}],
        "verdict": "yes",
        "rationale": "r",
    })
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_invalid_verdict(isc):
    """Verdict other than yes/no raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({
        "evidence": [], "verdict": "maybe", "rationale": "r",
    })
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_malformed_json(isc):
    """Non-JSON response body raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = json.dumps({"result": "this is not json at all"})
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_non_dict_evidence_item(isc):
    """Evidence item that is not a dict raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({
        "evidence": ["just a string, not a dict"],
        "verdict": "yes",
        "rationale": "r",
    })
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_evidence_not_a_list(isc):
    """Evidence that is not a list raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({
        "evidence": "not a list", "verdict": "yes", "rationale": "r",
    })
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_top_level_not_dict(isc):
    """Top-level non-object payload raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = json.dumps({"result": json.dumps([])})
    with pytest.raises(ValueError):
        parse(response)


def test_parse_implementability_raises_on_empty_rationale(isc):
    """Empty rationale string raises ValueError."""
    parse = getattr(isc, "_parse_implementability")
    response = _step2_envelope({
        "evidence": [], "verdict": "no", "rationale": "   ",
    })
    with pytest.raises(ValueError):
        parse(response)


# ---- _handle_step2 (new dispatch) -----------------------------------------


def test_handle_step2_returns_none_on_yes(isc):
    """Yes verdict returns None."""
    handle = getattr(isc, "_handle_step2")
    response = _make_step2_response(evidence=_EVIDENCE_FIXTURE, verdict="yes")
    assert handle(response) is None


def test_handle_step2_returns_sentinel_on_no(isc):
    """No verdict with empty evidence returns NotImplementable sentinel."""
    handle = getattr(isc, "_handle_step2")
    response = _make_step2_response(evidence=[], verdict="no")
    assert isinstance(handle(response), isc.NotImplementable)


def test_handle_step2_sentinel_carries_rationale(isc):
    """Sentinel carries the rationale from the response."""
    handle = getattr(isc, "_handle_step2")
    response = _make_step2_response(
        evidence=[], verdict="no", rationale="overview only here",
    )
    assert handle(response).rationale == "overview only here"


def test_handle_step2_sentinel_carries_evidence(isc):
    """Sentinel carries the (empty) evidence list."""
    handle = getattr(isc, "_handle_step2")
    response = _make_step2_response(evidence=[], verdict="no")
    assert handle(response).evidence == []


def test_handle_step2_override_returns_none(isc):
    """Override case (no with evidence) returns None, not sentinel."""
    handle = getattr(isc, "_handle_step2")
    response = _make_step2_response(evidence=_EVIDENCE_FIXTURE, verdict="no")
    assert handle(response) is None


def test_handle_step2_exits_on_schema_violation(isc):
    """Schema violation exits the process non-zero."""
    handle = getattr(isc, "_handle_step2")
    response = _step2_envelope({"verdict": "no"})
    with pytest.raises(SystemExit):
        handle(response)


_PARSE_FAIL_RAW = '{"result": "garbage that is not valid JSON at all"}'


def _handle_step2_capture_stderr(isc, capsys, raw):
    """Invoke _handle_step2 expecting SystemExit; return captured stderr."""
    try:
        getattr(isc, "_handle_step2")(raw)
    except SystemExit:
        pass
    return capsys.readouterr().err


def test_handle_step2_dumps_raw_stdout_on_parse_failure(isc, capsys):
    """Parse failure dumps the raw stdout to stderr for debugging."""
    err = _handle_step2_capture_stderr(isc, capsys, _PARSE_FAIL_RAW)
    assert _PARSE_FAIL_RAW in err


def test_handle_step2_dumps_error_message_on_parse_failure(isc, capsys):
    """Parse failure prints the parser ValueError text to stderr."""
    err = _handle_step2_capture_stderr(isc, capsys, _PARSE_FAIL_RAW)
    assert "ERROR:" in err


# ---- NotImplementable dataclass --------------------------------------------


def test_not_implementable_has_rationale_field(isc):
    """NotImplementable carries the rationale."""
    sentinel = isc.NotImplementable(rationale="r", evidence=[])
    assert sentinel.rationale == "r"


def test_not_implementable_has_evidence_field(isc):
    """NotImplementable carries the evidence list."""
    items = [{"quote": "Q", "why_testable": "W"}]
    sentinel = isc.NotImplementable(rationale="r", evidence=items)
    assert sentinel.evidence == items


def test_not_implementable_evidence_defaults_empty(isc):
    """NotImplementable.evidence defaults to an empty list."""
    sentinel = isc.NotImplementable(rationale="r")
    assert sentinel.evidence == []


# ---- build_steps Step 2 prompt ---------------------------------------------


def _step2_prompt(isc, tmp_path):
    """Return the Step 2 prompt produced by build_steps."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    steps = isc.build_steps("12.2", str(lrm))
    return next(p for d, p in steps if d == "Checking implementability")


def test_build_steps_step2_prompt_requests_evidence_field(isc, tmp_path):
    """Step 2 prompt asks for an 'evidence' field."""
    assert "evidence" in _step2_prompt(isc, tmp_path)


def test_build_steps_step2_prompt_requests_verdict_field(isc, tmp_path):
    """Step 2 prompt asks for a 'verdict' field."""
    assert "verdict" in _step2_prompt(isc, tmp_path)


def test_build_steps_step2_prompt_states_override_rule(isc, tmp_path):
    """Step 2 prompt states the 'evidence non-empty → verdict yes' rule."""
    assert "non-empty" in _step2_prompt(isc, tmp_path)


def test_build_steps_step2_prompt_warns_against_dismissing_definitions(isc, tmp_path):
    """Step 2 prompt warns against the 'merely definitional' failure mode."""
    assert "definitional" in _step2_prompt(isc, tmp_path)


def test_parse_args_rejects_figures_flag(isc, tmp_path):
    """--figures flag is no longer accepted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(lrm), "--subclause", "4", "--issue", "6",
            "--figures", "4_1=fig.gv",
        ])


def test_parse_args_rejects_tables_flag(isc, tmp_path):
    """--tables flag is no longer accepted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(lrm), "--subclause", "4", "--issue", "6",
            "--tables", "4_1=tbl.md",
        ])


# ---- _extract_result_text --------------------------------------------------


def test_extract_result_text_json_envelope(isc):
    """Extracts result from JSON envelope."""
    extract = getattr(isc, "_extract_result_text")
    assert extract('{"result": "- Did X"}') == "- Did X"


def test_extract_result_text_json_array(isc):
    """Extracts result from JSON array envelope."""
    extract = getattr(isc, "_extract_result_text")
    stdout = json.dumps([{"type": "init"}, {"result": "- Did Y"}])
    assert extract(stdout) == "- Did Y"


def test_extract_result_text_no_result_key(isc):
    """Falls back to raw text when no result key."""
    extract = getattr(isc, "_extract_result_text")
    assert extract('{"session_id": "x"}') == '{"session_id": "x"}'


def test_extract_result_text_plain_text(isc):
    """Returns plain text when not valid JSON."""
    extract = getattr(isc, "_extract_result_text")
    assert extract("- Did Z because needed") == "- Did Z because needed"


def test_extract_result_text_array_no_result(isc):
    """Falls back to raw text when array has no result key."""
    extract = getattr(isc, "_extract_result_text")
    stdout = json.dumps([{"type": "init"}, {"session_id": "x"}])
    assert extract(stdout) == stdout.strip()


# ---- commit_implementation -------------------------------------------------


def _commit_impl_and_capture(isc, *, subclause="6.6.1", action="",
                             changes=None):
    """Run commit_implementation with standard mocks; return mock dict."""
    if changes is None:
        changes = (["a.cpp"], [], [])
    with (
        patch("implement_subclause.get_porcelain_changes",
              return_value=changes) as m_files,
        patch("implement_subclause.commit_and_push",
              return_value="abc123") as m_cap,
        patch("implement_subclause.subprocess.run",
              return_value=MagicMock(returncode=0)) as m_gh,
    ):
        isc.commit_implementation(subclause, 8, action=action)
    return {"files": m_files, "cap": m_cap, "gh": m_gh}


def test_commit_implementation_calls_commit_and_push(isc):
    """commit_implementation passes files and message to commit_and_push."""
    assert _commit_impl_and_capture(isc)["cap"].called


def test_commit_implementation_message_has_subclause(isc):
    """Commit message uses section sign for numeric subclauses."""
    assert "Implement §6.6.1" in _commit_impl_and_capture(isc)["cap"].call_args[0][2]


def test_commit_implementation_message_annex_prefix(isc):
    """Commit message uses Annex prefix for annex subclauses."""
    msg = _commit_impl_and_capture(isc, subclause="A.8.1")["cap"].call_args[0][2]
    assert "Implement Annex A.8.1" in msg


def test_commit_implementation_message_no_co_authored_by(isc):
    """Commit message does not contain Co-Authored-By trailer."""
    assert "Co-Authored-By" not in _commit_impl_and_capture(isc)["cap"].call_args[0][2]


def test_commit_implementation_message_has_action(isc):
    """Commit message contains action text when provided."""
    mocks = _commit_impl_and_capture(isc, action="- Added foo.cpp")
    assert "- Added foo.cpp" in mocks["cap"].call_args[0][2]


def test_commit_implementation_message_omits_action_when_empty(isc):
    """Commit message has no double blank lines when action is empty."""
    msg = _commit_impl_and_capture(isc)["cap"].call_args[0][2]
    assert "\n\n\n" not in msg


def test_commit_implementation_changed_includes_added_and_modified(isc):
    """commit_and_push receives added + modified as changed files."""
    mocks = _commit_impl_and_capture(
        isc, changes=(["a.cpp"], ["b.cpp"], []),
    )
    assert mocks["cap"].call_args[0][0] == ["a.cpp", "b.cpp"]


def test_commit_implementation_message_closes_issue(isc):
    """Commit message contains Closes #issue."""
    msg = _commit_impl_and_capture(isc)["cap"].call_args[0][2]
    assert "Closes #8" in msg


def test_commit_implementation_filters_garbage_files(isc):
    """commit_implementation ignores files without valid extensions."""
    mocks = _commit_impl_and_capture(
        isc, changes=(["a.cpp", "2", "{a,"], ["b.h"], ["old"]),
    )
    assert mocks["cap"].call_args[0][0] == ["a.cpp", "b.h"]


def test_commit_implementation_skips_commit_when_no_valid_changes(isc):
    """commit_implementation skips commit when only garbage files exist."""
    mocks = _commit_impl_and_capture(
        isc, changes=(["2", "{a,"], [], ["ev"]),
    )
    assert not mocks["cap"].called


def test_commit_implementation_closes_issue_when_no_changes(isc):
    """commit_implementation closes issue via gh when no valid changes."""
    mocks = _commit_impl_and_capture(
        isc, changes=([], [], []), action="No changes needed.",
    )
    cmd = mocks["gh"].call_args[0][0]
    assert "close" in cmd


def test_commit_implementation_close_comment_has_action(isc):
    """commit_implementation passes action summary as close comment."""
    mocks = _commit_impl_and_capture(
        isc, changes=([], [], []), action="Nothing to do.",
    )
    cmd = mocks["gh"].call_args[0][0]
    assert "Nothing to do." in cmd


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclause", run_name="__main__")
