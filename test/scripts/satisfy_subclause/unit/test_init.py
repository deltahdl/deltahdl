"""Unit tests for satisfy_subclause (outer orchestrator)."""

import json
import runpy
from pathlib import Path
from unittest.mock import patch

import pytest

from lib.python.satisfy import SATISFIED, SubclauseDiagnostic
from lib.python.test_fixtures.satisfy import make_lrm, stub_completed


# ---- helpers ---------------------------------------------------------------


def _diag(failing: bool = False) -> SubclauseDiagnostic:
    """Return a satisfied or one-failure diagnostic."""
    rule = ["rule 7 has no production code"] if failing else SATISFIED
    return SubclauseDiagnostic(
        rule_coverage=rule,
        test_coverage=SATISFIED,
        test_placement=SATISFIED,
        naming=SATISFIED,
        deduplication=SATISFIED,
    )


def _args(tmp_path, **overrides):
    """Build a CLI argv with sane defaults."""
    return [
        "--lrm", overrides.get("lrm", str(make_lrm(tmp_path))),
        "--subclause", overrides.get("subclause", "33.4.1.5"),
        "--model", overrides.get("model", "opus"),
        "--in-progress", overrides.get("in_progress", ""),
    ]


def _completed(stdout="", returncode=0):
    """Build a stubbed CompletedProcess via the shared helper."""
    return stub_completed(stdout=stdout, returncode=returncode)


# ---- parse_args ------------------------------------------------------------


def test_parse_args_default_in_progress(ssc, tmp_path):
    """--in-progress defaults to an empty string."""
    args = ssc.parse_args(_args(tmp_path))
    assert args.in_progress == ""


def test_parse_args_in_progress_value(ssc, tmp_path):
    """--in-progress preserves the comma-separated value."""
    args = ssc.parse_args(_args(tmp_path, in_progress="33.4,33.5"))
    assert args.in_progress == "33.4,33.5"


def test_parse_args_default_model(ssc, tmp_path):
    """--model defaults to 'opus'."""
    args = ssc.parse_args(_args(tmp_path))
    assert args.model == "opus"


# ---- issue helpers ---------------------------------------------------------


def test_issue_title_for(ssc):
    """issue_title_for produces the canonical 'Satisfy §X' title."""
    assert ssc.issue_title_for("33.4.1.5") == "Satisfy §33.4.1.5"


def test_parse_issue_number_from_create_output(ssc):
    """The number is extracted from a gh issue create URL."""
    output = "Creating issue\nhttps://github.com/o/r/issues/123\n"
    assert ssc.parse_issue_number_from_create_output(output) == 123


# ---- find_or_create_issue --------------------------------------------------


def _patched_gh(list_payload="[]", list_rc=0, create_url="", create_rc=0):
    """Patch subprocess.run with a sequence of gh responses."""
    list_completed = _completed(stdout=list_payload, returncode=list_rc)
    create_completed = _completed(stdout=create_url, returncode=create_rc)
    return patch(
        "satisfy_subclause.subprocess.run",
        side_effect=[list_completed, create_completed],
    )


def test_find_or_create_issue_creates_new(ssc):
    """find_or_create_issue creates a new issue when none exists."""
    url = "https://github.com/o/r/issues/777"
    with _patched_gh(create_url=url):
        assert ssc.find_or_create_issue("33.4.1.5") == 777


def test_find_or_create_issue_reuses_open(ssc):
    """find_or_create_issue returns an existing open issue's number."""
    body = json.dumps([
        {"number": 99, "title": "Satisfy §33.4.1.5", "state": "OPEN"},
    ])
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(stdout=body),
    ):
        assert ssc.find_or_create_issue("33.4.1.5") == 99


def test_find_or_create_issue_reopens_closed(ssc):
    """find_or_create_issue reopens a closed match before returning it."""
    body = json.dumps([
        {"number": 55, "title": "Satisfy §33.4.1.5", "state": "CLOSED"},
    ])
    with patch(
        "satisfy_subclause.subprocess.run",
        side_effect=[_completed(stdout=body), _completed()],
    ) as mock_run:
        ssc.find_or_create_issue("33.4.1.5")
    cmd = mock_run.call_args_list[1][0][0]
    assert cmd[:3] == ["gh", "issue", "reopen"]


def test_find_or_create_issue_exits_on_list_failure(ssc):
    """A non-zero gh issue list exit is loud-fatal."""
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(returncode=1),
    ):
        with pytest.raises(SystemExit):
            ssc.find_or_create_issue("33.4.1.5")


def test_find_or_create_issue_exits_on_create_failure(ssc):
    """A non-zero gh issue create exit is loud-fatal."""
    with patch(
        "satisfy_subclause.subprocess.run",
        side_effect=[_completed(stdout="[]"), _completed(returncode=1)],
    ):
        with pytest.raises(SystemExit):
            ssc.find_or_create_issue("33.4.1.5")


def test_find_or_create_issue_creates_when_no_title_matches(ssc):
    """A list with mismatched-title entries falls through to create."""
    body = json.dumps([
        {"number": 1, "title": "Different title", "state": "OPEN"},
    ])
    create_url = "https://github.com/o/r/issues/333"
    with patch(
        "satisfy_subclause.subprocess.run",
        side_effect=[
            _completed(stdout=body), _completed(stdout=create_url),
        ],
    ):
        assert ssc.find_or_create_issue("33.4.1.5") == 333


# ---- label_issue_pipeline_stuck --------------------------------------------


def test_label_issue_adds_label(ssc):
    """label_issue_pipeline_stuck adds the pipeline-stuck label."""
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(),
    ) as mock_run:
        ssc.label_issue_pipeline_stuck(42, _diag(failing=True))
    label_cmd = mock_run.call_args_list[0][0][0]
    assert "pipeline-stuck" in label_cmd


def test_label_issue_posts_comment(ssc):
    """label_issue_pipeline_stuck posts a diagnostic comment."""
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(),
    ) as mock_run:
        ssc.label_issue_pipeline_stuck(42, _diag(failing=True))
    comment_cmd = mock_run.call_args_list[1][0][0]
    assert "comment" in comment_cmd


# ---- invoke_oracle ---------------------------------------------------------


def _oracle_payload(failing=False):
    """Build an is_subclause_satisfied stdout payload."""
    diag = _diag(failing=failing)
    payload = {
        "rule_coverage": diag.rule_coverage,
        "test_coverage": diag.test_coverage,
        "test_placement": diag.test_placement,
        "naming": diag.naming,
        "deduplication": diag.deduplication,
        "verdict": diag.verdict,
    }
    return json.dumps(payload)


def test_invoke_oracle_parses_diagnostic(ssc):
    """invoke_oracle parses the JSON the oracle prints to stdout."""
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(stdout=_oracle_payload()),
    ):
        diag = ssc.invoke_oracle("4.1", "lrm.pdf", model="opus")
    assert diag.verdict == "yes"


def test_invoke_oracle_exits_on_nonzero(ssc):
    """A non-zero oracle exit is loud-fatal."""
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(returncode=1),
    ):
        with pytest.raises(SystemExit):
            ssc.invoke_oracle("4.1", "lrm.pdf", model="opus")


# ---- write_diagnostic ------------------------------------------------------


def test_write_diagnostic_round_trips(ssc, tmp_path):
    """write_diagnostic produces a file whose JSON round-trips."""
    path = ssc.write_diagnostic(tmp_path, _diag(failing=True))
    payload = json.loads(path.read_text())
    assert payload["rule_coverage"] == ["rule 7 has no production code"]


# ---- run_pipeline_pass -----------------------------------------------------


def test_run_pipeline_pass_satisfied_status(ssc, tmp_path):
    """run_pipeline_pass returns satisfied when inner orch reports satisfied."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.invoke_inner_orchestrator",
        return_value={"status": "satisfied"},
    ):
        result = ssc.run_pipeline_pass(
            args, _diag(failing=True), 42, [], tmp_path,
        )
    assert result == {"status": "satisfied"}


def test_run_pipeline_pass_propagates_cycle_when_member(ssc, tmp_path):
    """A cycle marker propagates when our subclause is in members + nested."""
    args = ssc.parse_args(_args(tmp_path, in_progress="33.6"))
    with patch(
        "satisfy_subclause.invoke_inner_orchestrator",
        return_value={
            "status": "cycle", "members": ["33.4.1.5", "33.6"],
        },
    ):
        result = ssc.run_pipeline_pass(
            args, _diag(failing=True), 42, ["33.6"], tmp_path,
        )
    assert result["status"] == "cycle"


def test_run_pipeline_pass_dispatches_cycle_at_outermost(ssc, tmp_path):
    """A cycle marker triggers dispatch when we are the outermost frame."""
    args = ssc.parse_args(_args(tmp_path))
    with (
        patch(
            "satisfy_subclause.invoke_inner_orchestrator",
            return_value={
                "status": "cycle", "members": ["33.4.1.5", "33.6"],
            },
        ),
        patch(
            "satisfy_subclause.dispatch_cycle",
        ) as mock_dispatch,
    ):
        result = ssc.run_pipeline_pass(
            args, _diag(failing=True), 42, [], tmp_path,
        )
    assert mock_dispatch.called and result == {"status": "satisfied"}


# ---- dispatch_cycle --------------------------------------------------------


def test_dispatch_cycle_invokes_set_mutator(ssc, tmp_path):
    """dispatch_cycle invokes the set mutator with one diagnostic per member."""
    args = ssc.parse_args(_args(tmp_path))
    with (
        patch(
            "satisfy_subclause.invoke_oracle",
            return_value=_diag(failing=True),
        ),
        patch(
            "satisfy_subclause.find_or_create_issue",
            side_effect=[100, 101],
        ),
        patch(
            "satisfy_subclause.invoke_cycle_mutator",
        ) as mock_mut,
    ):
        ssc.dispatch_cycle(args, ["33.4.1.5", "33.6"], tmp_path)
    diagnostic_paths = mock_mut.call_args[0][2]
    assert len(diagnostic_paths) == 2


def test_dispatch_cycle_passes_issues(ssc, tmp_path):
    """dispatch_cycle passes the per-member issue numbers to the set mutator."""
    args = ssc.parse_args(_args(tmp_path))
    with (
        patch(
            "satisfy_subclause.invoke_oracle",
            return_value=_diag(failing=True),
        ),
        patch(
            "satisfy_subclause.find_or_create_issue",
            side_effect=[200, 201],
        ),
        patch(
            "satisfy_subclause.invoke_cycle_mutator",
        ) as mock_mut,
    ):
        ssc.dispatch_cycle(args, ["33.4.1.5", "33.6"], tmp_path)
    assert mock_mut.call_args[0][3] == [200, 201]


def test_invoke_cycle_mutator_runs_subprocess(ssc, tmp_path):
    """invoke_cycle_mutator subprocesses the set-mutator module."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(),
    ) as mock_run:
        ssc.invoke_cycle_mutator(
            args, ["1.1", "1.2"],
            [Path("/tmp/a.json"), Path("/tmp/b.json")], [10, 11],
        )
    cmd = mock_run.call_args[0][0]
    assert "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies" in cmd


def test_invoke_cycle_mutator_exits_on_nonzero(ssc, tmp_path):
    """A non-zero set-mutator exit is fatal."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(returncode=2),
    ):
        with pytest.raises(SystemExit):
            ssc.invoke_cycle_mutator(
                args, ["1.1", "1.2"],
                [Path("/tmp/a.json"), Path("/tmp/b.json")], [10, 11],
            )


def test_invoke_inner_orchestrator_parses_status(ssc, tmp_path):
    """invoke_inner_orchestrator returns the parsed status dict."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps({"status": "satisfied"})),
    ):
        result = ssc.invoke_inner_orchestrator(
            args, Path("/tmp/d.json"), 42, ["33.6"],
        )
    assert result == {"status": "satisfied"}


def test_invoke_inner_orchestrator_handles_empty_stdout(ssc, tmp_path):
    """invoke_inner_orchestrator returns {} for empty stdout."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(stdout=""),
    ):
        result = ssc.invoke_inner_orchestrator(
            args, Path("/tmp/d.json"), 42, [],
        )
    assert result == {}


def test_invoke_inner_orchestrator_handles_non_dict_stdout(ssc, tmp_path):
    """invoke_inner_orchestrator returns {} for a non-dict JSON payload."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps([1, 2])),
    ):
        result = ssc.invoke_inner_orchestrator(
            args, Path("/tmp/d.json"), 42, [],
        )
    assert result == {}


def test_invoke_inner_orchestrator_exits_on_nonzero(ssc, tmp_path):
    """A non-zero inner orchestrator exit is fatal."""
    args = ssc.parse_args(_args(tmp_path))
    with patch(
        "satisfy_subclause.subprocess.run",
        return_value=_completed(returncode=2),
    ):
        with pytest.raises(SystemExit):
            ssc.invoke_inner_orchestrator(
                args, Path("/tmp/d.json"), 42, [],
            )


# ---- main ------------------------------------------------------------------


def _patched_pipeline(diagnostics, pass_results=None):
    """Patch invoke_oracle + run_pipeline_pass + find_or_create_issue."""
    return (
        patch(
            "satisfy_subclause.invoke_oracle",
            side_effect=diagnostics,
        ),
        patch(
            "satisfy_subclause.find_or_create_issue",
            return_value=42,
        ),
        patch(
            "satisfy_subclause.run_pipeline_pass",
            side_effect=pass_results or [],
        ),
        patch("satisfy_subclause.label_issue_pipeline_stuck"),
    )


def test_main_skips_when_already_satisfied(ssc, tmp_path):
    """main() does not run the pipeline when the oracle returns yes."""
    oracle, issue, pipeline, label = _patched_pipeline([_diag()])
    with oracle:
        with issue:
            with pipeline as ppass:
                with label:
                    ssc.main(_args(tmp_path))
    assert not ppass.called


def test_main_runs_pipeline_when_unsatisfied(ssc, tmp_path):
    """main() runs the pipeline when the oracle returns no first."""
    oracle, issue, pipeline, label = _patched_pipeline(
        [_diag(failing=True), _diag()],
        pass_results=[{"status": "satisfied"}],
    )
    with oracle:
        with issue:
            with pipeline as ppass:
                with label:
                    ssc.main(_args(tmp_path))
    assert ppass.called


def test_main_emits_satisfied_when_converged(ssc, tmp_path, capsys):
    """main() emits the satisfied status after the pipeline converges."""
    oracle, issue, pipeline, label = _patched_pipeline(
        [_diag(failing=True), _diag()],
        pass_results=[{"status": "satisfied"}],
    )
    with oracle:
        with issue:
            with pipeline:
                with label:
                    ssc.main(_args(tmp_path))
    assert json.loads(capsys.readouterr().out)["status"] == "satisfied"


def test_main_propagates_cycle(ssc, tmp_path, capsys):
    """main() emits a cycle status when run_pipeline_pass returns cycle."""
    cycle_payload = {"status": "cycle", "members": ["33.4", "33.5"]}
    oracle, issue, pipeline, label = _patched_pipeline(
        [_diag(failing=True)],
        pass_results=[cycle_payload],
    )
    with oracle:
        with issue:
            with pipeline:
                with label:
                    ssc.main(_args(tmp_path, in_progress="33.4"))
    assert json.loads(capsys.readouterr().out)["status"] == "cycle"


def test_main_retries_once_then_labels_stuck(ssc, tmp_path):
    """main() retries the pipeline once then labels the issue pipeline-stuck."""
    failing = _diag(failing=True)
    oracle, issue, pipeline, label = _patched_pipeline(
        [failing, failing, failing],
        pass_results=[{"status": "satisfied"}, {"status": "satisfied"}],
    )
    with oracle:
        with issue:
            with pipeline:
                with label as mock_label:
                    try:
                        ssc.main(_args(tmp_path))
                    except SystemExit:
                        pass
    assert mock_label.called


def test_main_exits_nonzero_when_stuck(ssc, tmp_path):
    """main() exits with a non-zero code when the pipeline gets stuck."""
    failing = _diag(failing=True)
    oracle, issue, pipeline, label = _patched_pipeline(
        [failing, failing, failing],
        pass_results=[{"status": "satisfied"}, {"status": "satisfied"}],
    )
    captured_code = None
    with oracle:
        with issue:
            with pipeline:
                with label:
                    try:
                        ssc.main(_args(tmp_path))
                    except SystemExit as exc:
                        captured_code = exc.code
    assert captured_code != 0


def test_main_logs_subclause_to_stderr(ssc, tmp_path, capsys):
    """main() prints a one-line outer-orchestrator banner to stderr."""
    oracle, issue, pipeline, label = _patched_pipeline([_diag()])
    with oracle:
        with issue:
            with pipeline:
                with label:
                    ssc.main(_args(tmp_path))
    assert "§33.4.1.5" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_subclause", run_name="__main__")
