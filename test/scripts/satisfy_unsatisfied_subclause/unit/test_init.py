"""Unit tests for satisfy_unsatisfied_subclause (inner orchestrator)."""

import json
import runpy
from unittest.mock import MagicMock, patch

import pytest

from lib.python.test_fixtures.satisfy import (
    failing_payload,
    make_lrm,
    write_diagnostic,
)


# ---- helpers ---------------------------------------------------------------


def _failing():
    """Return a payload with a single rule_coverage failure."""
    return failing_payload(
        "rule_coverage", failures=["needs an unrelated subclause"],
    )


def _args(tmp_path, **overrides):
    """Build a CLI argv with a sane default diagnostic file."""
    diag = write_diagnostic(tmp_path, _failing())
    return [
        "--lrm", overrides.get("lrm", str(make_lrm(tmp_path))),
        "--subclause", overrides.get("subclause", "33.4.1.5"),
        "--diagnostic-file", str(diag),
        "--issue", str(overrides.get("issue", 42)),
        "--model", overrides.get("model", "opus"),
        "--in-progress", overrides.get("in_progress", ""),
    ]


def _completed(stdout="", returncode=0):
    """Build a stubbed CompletedProcess."""
    completed = MagicMock()
    completed.returncode = returncode
    completed.stdout = stdout
    completed.stderr = ""
    return completed


# ---- parse_args -----------------------------------------------------------


def test_parse_args_requires_diagnostic_file(sus, tmp_path):
    """--diagnostic-file is required."""
    with pytest.raises(SystemExit):
        sus.parse_args([
            "--lrm", str(make_lrm(tmp_path)),
            "--subclause", "33.4.1.5",
            "--issue", "1",
        ])


def test_parse_args_default_in_progress_empty(sus, tmp_path):
    """--in-progress defaults to an empty string."""
    args = sus.parse_args(_args(tmp_path, in_progress=""))
    assert args.in_progress == ""


def test_parse_args_in_progress_value(sus, tmp_path):
    """--in-progress preserves a comma-separated string."""
    args = sus.parse_args(_args(tmp_path, in_progress="33.4,33.5"))
    assert args.in_progress == "33.4,33.5"


# ---- parse_in_progress ----------------------------------------------------


def test_parse_in_progress_empty(sus):
    """An empty string parses to an empty list."""
    assert sus.parse_in_progress("") == []


def test_parse_in_progress_single(sus):
    """A single value parses to a one-element list."""
    assert sus.parse_in_progress("33.4") == ["33.4"]


def test_parse_in_progress_strips_whitespace(sus):
    """Whitespace around entries is stripped."""
    assert sus.parse_in_progress("33.4, 33.5") == ["33.4", "33.5"]


# ---- detect_cycle_members -------------------------------------------------


def test_detect_cycle_members_no_overlap(sus):
    """An empty intersection returns an empty list."""
    assert sus.detect_cycle_members(["1.1"], ["2.2"]) == []


def test_detect_cycle_members_full_overlap(sus):
    """A fully-overlapping deps list returns the full intersection."""
    assert sus.detect_cycle_members(["1.1"], ["1.1"]) == ["1.1"]


def test_detect_cycle_members_partial_overlap(sus):
    """A partial overlap returns the intersection only."""
    assert sus.detect_cycle_members(["1.1", "2.2"], ["2.2"]) == ["2.2"]


# ---- emit_cycle_marker ----------------------------------------------------


def test_emit_cycle_marker_includes_subclause(sus, capsys):
    """The cycle marker includes the current subclause in members."""
    sus.emit_cycle_marker("33.4", ["33.5"])
    payload = json.loads(capsys.readouterr().out)
    assert "33.4" in payload["members"]


def test_emit_cycle_marker_status(sus, capsys):
    """The cycle marker status field is 'cycle'."""
    sus.emit_cycle_marker("33.4", ["33.5"])
    assert json.loads(capsys.readouterr().out)["status"] == "cycle"


def test_emit_satisfied_marker_status(sus, capsys):
    """The satisfied marker status field is 'satisfied'."""
    sus.emit_satisfied_marker()
    assert json.loads(capsys.readouterr().out)["status"] == "satisfied"


# ---- invoke_compute_dependencies -------------------------------------------


def test_invoke_compute_dependencies_returns_list(sus):
    """invoke_compute_dependencies parses the JSON list from stdout."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps(["33.6.1"])),
    ):
        deps = sus.invoke_compute_dependencies("33.4", "lrm.pdf", model="opus")
    assert deps == ["33.6.1"]


def test_invoke_compute_dependencies_exits_on_nonzero(sus):
    """A non-zero exit code from compute_subclause_dependencies is fatal."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(returncode=1),
    ):
        with pytest.raises(SystemExit):
            sus.invoke_compute_dependencies("33.4", "lrm.pdf", model="opus")


def test_invoke_compute_dependencies_rejects_non_list(sus):
    """A non-list JSON payload is fatal."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps({"x": 1})),
    ):
        with pytest.raises(SystemExit):
            sus.invoke_compute_dependencies("33.4", "lrm.pdf", model="opus")


# ---- invoke_satisfy_subclause ---------------------------------------------


def test_invoke_satisfy_subclause_parses_satisfied(sus):
    """invoke_satisfy_subclause parses a satisfied JSON payload."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps({"status": "satisfied"})),
    ):
        result = sus.invoke_satisfy_subclause(
            "33.6.1", "lrm.pdf", model="opus", in_progress=["33.4"],
        )
    assert result == {"status": "satisfied"}


def test_invoke_satisfy_subclause_passes_in_progress(sus):
    """invoke_satisfy_subclause forwards --in-progress to the subprocess."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps({})),
    ) as mock_run:
        sus.invoke_satisfy_subclause(
            "33.6.1", "lrm.pdf", model="opus", in_progress=["33.4", "33.5"],
        )
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--in-progress") + 1] == "33.4,33.5"


def test_invoke_satisfy_subclause_handles_empty_stdout(sus):
    """invoke_satisfy_subclause returns {} when stdout is empty."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(stdout=""),
    ):
        result = sus.invoke_satisfy_subclause(
            "33.6.1", "lrm.pdf", model="opus", in_progress=[],
        )
    assert result == {}


def test_invoke_satisfy_subclause_handles_non_dict(sus):
    """invoke_satisfy_subclause coerces a non-dict stdout to {}."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(stdout=json.dumps(["a"])),
    ):
        result = sus.invoke_satisfy_subclause(
            "33.6.1", "lrm.pdf", model="opus", in_progress=[],
        )
    assert result == {}


def test_invoke_satisfy_subclause_exits_on_nonzero(sus):
    """A non-zero exit code from the subprocess is fatal."""
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(returncode=2),
    ):
        with pytest.raises(SystemExit):
            sus.invoke_satisfy_subclause(
                "33.6.1", "lrm.pdf", model="opus", in_progress=[],
            )


# ---- mutator-invocation helpers --------------------------------------------


def test_invoke_no_deps_mutator_calls_correct_module(sus, tmp_path):
    """invoke_no_deps_mutator targets the no-deps mutator module."""
    args = sus.parse_args(_args(tmp_path))
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(),
    ) as mock_run:
        sus.invoke_no_deps_mutator(args)
    cmd = mock_run.call_args[0][0]
    assert "satisfy_unsatisfied_subclause_without_dependencies" in cmd


def test_invoke_with_deps_mutator_calls_correct_module(sus, tmp_path):
    """invoke_with_deps_mutator targets the with-deps mutator module."""
    args = sus.parse_args(_args(tmp_path))
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(),
    ) as mock_run:
        sus.invoke_with_deps_mutator(args, ["33.6.1"])
    cmd = mock_run.call_args[0][0]
    assert "satisfy_unsatisfied_subclause_with_satisfied_dependencies" in cmd


def test_invoke_with_deps_mutator_passes_satisfied(sus, tmp_path):
    """invoke_with_deps_mutator forwards the satisfied-deps list."""
    args = sus.parse_args(_args(tmp_path))
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(),
    ) as mock_run:
        sus.invoke_with_deps_mutator(args, ["33.6.1", "33.7"])
    cmd = mock_run.call_args[0][0]
    assert cmd[cmd.index("--satisfied-dependencies") + 1] == "33.6.1,33.7"


def test_invoke_no_deps_mutator_exits_on_nonzero(sus, tmp_path):
    """invoke_no_deps_mutator exits with the mutator's non-zero return code."""
    args = sus.parse_args(_args(tmp_path))
    with patch(
        "satisfy_unsatisfied_subclause.subprocess.run",
        return_value=_completed(returncode=3),
    ):
        with pytest.raises(SystemExit):
            sus.invoke_no_deps_mutator(args)


# ---- main ------------------------------------------------------------------


def _patched_orchestrator(deps, dep_results=None):
    """Patch invoke_compute_dependencies and invoke_satisfy_subclause."""
    return (
        patch(
            "satisfy_unsatisfied_subclause.invoke_compute_dependencies",
            return_value=deps,
        ),
        patch(
            "satisfy_unsatisfied_subclause.invoke_satisfy_subclause",
            side_effect=dep_results or [{"status": "satisfied"}] * len(deps),
        ),
    )


def test_main_no_deps_invokes_no_deps_mutator(sus, tmp_path):
    """main() with no deps dispatches to the no-deps mutator."""
    mock_deps, mock_satisfy = _patched_orchestrator([])
    with mock_deps:
        with mock_satisfy:
            with patch(
                "satisfy_unsatisfied_subclause.invoke_no_deps_mutator",
            ) as mock_no_deps:
                with patch(
                    "satisfy_unsatisfied_subclause.invoke_with_deps_mutator",
                ) as mock_with_deps:
                    sus.main(_args(tmp_path))
    assert mock_no_deps.called and not mock_with_deps.called


def test_main_with_deps_invokes_with_deps_mutator(sus, tmp_path):
    """main() with deps dispatches to the with-deps mutator."""
    mock_deps, mock_satisfy = _patched_orchestrator(["33.6.1"])
    with mock_deps:
        with mock_satisfy:
            with patch(
                "satisfy_unsatisfied_subclause.invoke_no_deps_mutator",
            ) as mock_no_deps:
                with patch(
                    "satisfy_unsatisfied_subclause.invoke_with_deps_mutator",
                ) as mock_with_deps:
                    sus.main(_args(tmp_path))
    assert mock_with_deps.called and not mock_no_deps.called


def test_main_emits_satisfied_after_dispatch(sus, tmp_path, capsys):
    """main() emits the satisfied marker after the mutator returns."""
    mock_deps, mock_satisfy = _patched_orchestrator([])
    with mock_deps:
        with mock_satisfy:
            with patch(
                "satisfy_unsatisfied_subclause.invoke_no_deps_mutator",
            ):
                sus.main(_args(tmp_path))
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "satisfied"


def test_main_detects_cycle_in_own_deps(sus, tmp_path, capsys):
    """main() emits a cycle marker when a dep is in --in-progress."""
    mock_deps, mock_satisfy = _patched_orchestrator(["33.4"])
    with mock_deps:
        with mock_satisfy:
            sus.main(_args(tmp_path, in_progress="33.4"))
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "cycle" and "33.4" in payload["members"]


def test_main_propagates_cycle_from_dep(sus, tmp_path, capsys):
    """main() propagates a cycle marker emitted by a recursive dep call."""
    mock_deps, mock_satisfy = _patched_orchestrator(
        ["33.6.1"],
        dep_results=[{"status": "cycle", "members": ["33.4", "33.6.1"]}],
    )
    with mock_deps:
        with mock_satisfy:
            sus.main(_args(tmp_path))
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == "cycle"


def test_main_logs_subclause_to_stderr(sus, tmp_path, capsys):
    """main() prints a one-line orchestrator banner to stderr."""
    mock_deps, mock_satisfy = _patched_orchestrator([])
    with mock_deps:
        with mock_satisfy:
            with patch(
                "satisfy_unsatisfied_subclause.invoke_no_deps_mutator",
            ):
                sus.main(_args(tmp_path))
    assert "§33.4.1.5" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_unsatisfied_subclause", run_name="__main__")
