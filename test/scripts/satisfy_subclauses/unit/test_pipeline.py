"""Unit tests for the satisfy_subclauses pipeline."""

import json
import sys
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from satisfy_subclauses.pipeline import (
    _classify_token,
    _fetch_linked_issue,
    _fetch_master,
    _patch_master_body,
    _resolve_linked,
    _resolve_unlinked,
    _run_satisfy_subclause,
    satisfy_subclauses,
    satisfy_subclauses_from_issue,
)


_LRM = "lrm.pdf"
_LABELS = ["IEEE 1800-2023"]


# --- satisfy_subclauses (subprocess invocation per entry) ------------------


def _stub_run(returncode: int = 0) -> MagicMock:
    """Build a stubbed CompletedProcess with the given returncode."""
    completed = MagicMock()
    completed.returncode = returncode
    return completed


def _run_satisfy_subclauses_and_capture(
    subclauses: list[str], *,
    model: str = "opus", labels: list[str] | None = None,
) -> MagicMock:
    """Run satisfy_subclauses with subprocess stubbed; return the mock."""
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=_stub_run(),
    ) as mock_run:
        satisfy_subclauses(
            subclauses, _LRM, model=model, labels=labels or _LABELS,
        )
    return mock_run


def test_satisfy_subclauses_invokes_one_subprocess_per_entry() -> None:
    """satisfy_subclauses runs one subprocess per --subclauses entry."""
    mock_run = _run_satisfy_subclauses_and_capture(["33.1", "33.4"])
    assert mock_run.call_count == 2


def test_satisfy_subclauses_dispatches_python_dash_m_satisfy_subclause() -> None:
    """Each invocation is ``python -m satisfy_subclause``."""
    mock_run = _run_satisfy_subclauses_and_capture(["33.1", "33.4"])
    assert all(
        c.args[0][:3] == [sys.executable, "-m", "satisfy_subclause"]
        for c in mock_run.call_args_list
    )


def test_satisfy_subclauses_passes_subclause_arg() -> None:
    """Each subprocess receives the right --subclause value."""
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=_stub_run(),
    ) as mock_run:
        satisfy_subclauses(
            ["33.1", "A.7"], _LRM, model="opus", labels=_LABELS,
        )
    subclauses = [
        c.args[0][c.args[0].index("--subclause") + 1]
        for c in mock_run.call_args_list
    ]
    assert subclauses == ["33.1", "A.7"]


def _argv_value(mock_run: MagicMock, flag: str) -> str:
    """Return the value passed for *flag* in the first captured argv."""
    argv = mock_run.call_args_list[0].args[0]
    value: str = argv[argv.index(flag) + 1]
    return value


def test_satisfy_subclauses_forwards_lrm_to_subprocess() -> None:
    """The CLI surface forwards --lrm into the subprocess argv."""
    mock_run = _run_satisfy_subclauses_and_capture(
        ["33.1"], model="haiku", labels=["IEEE 1800-2023", "bug"],
    )
    assert _argv_value(mock_run, "--lrm") == _LRM


def test_satisfy_subclauses_forwards_model_to_subprocess() -> None:
    """The CLI surface forwards --model into the subprocess argv."""
    mock_run = _run_satisfy_subclauses_and_capture(
        ["33.1"], model="haiku", labels=["IEEE 1800-2023", "bug"],
    )
    assert _argv_value(mock_run, "--model") == "haiku"


def test_satisfy_subclauses_forwards_labels_to_subprocess() -> None:
    """The CLI surface joins --labels and forwards them into the subprocess argv."""
    mock_run = _run_satisfy_subclauses_and_capture(
        ["33.1"], model="haiku", labels=["IEEE 1800-2023", "bug"],
    )
    assert _argv_value(mock_run, "--labels") == "IEEE 1800-2023,bug"


def _run_satisfy_subclauses_failing(rc: int) -> int | str | None:
    """Run satisfy_subclauses against a failing subprocess; return its exit code."""
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=_stub_run(returncode=rc),
    ):
        with pytest.raises(SystemExit) as excinfo:
            satisfy_subclauses(
                ["33.1"], _LRM, model="opus", labels=_LABELS,
            )
    return excinfo.value.code


def test_satisfy_subclauses_exits_with_subprocess_returncode() -> None:
    """A non-zero satisfy_subclause exit propagates as SystemExit with the same rc."""
    assert _run_satisfy_subclauses_failing(7) == 7


def test_satisfy_subclauses_empty_list_runs_no_subprocess() -> None:
    """An empty subclause list invokes no subprocess."""
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=_stub_run(),
    ) as mock_run:
        satisfy_subclauses([], _LRM, model="opus", labels=_LABELS)
    assert not mock_run.called


def test_run_satisfy_subclause_invokes_one_subprocess_on_success() -> None:
    """_run_satisfy_subclause runs the subprocess exactly once on rc=0."""
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=_stub_run(),
    ) as mock_run:
        _run_satisfy_subclause(
            "33.1", _LRM, model="opus", labels=_LABELS,
        )
    assert mock_run.call_count == 1


# --- _classify_token --------------------------------------------------------


def test_classify_token_accepts_hash_reference() -> None:
    """`#NNN` parses as a hash entry with the captured number."""
    assert _classify_token("#1307") == ("hash", "1307")


def test_classify_token_accepts_section_marker() -> None:
    """`§X.Y` parses as a section entry with the captured subclause."""
    assert _classify_token("§6.18") == ("section", "6.18")


def test_classify_token_accepts_annex_marker() -> None:
    """`§A.6.7` parses as an annex section entry."""
    assert _classify_token("§A.6.7") == ("section", "A.6.7")


def test_classify_token_rejects_malformed_section() -> None:
    """A malformed §marker raises ValueError."""
    with pytest.raises(ValueError):
        _classify_token("§bogus!!")


def test_classify_token_rejects_garbage() -> None:
    """A non-§ non-# token raises ValueError."""
    with pytest.raises(ValueError):
        _classify_token("foo")


# --- _fetch_master ----------------------------------------------------------


def _gh_view_body_payload(body: str) -> str:
    """Build a `gh issue view --json body` payload."""
    return json.dumps({"body": body})


def test_fetch_master_returns_body_lines() -> None:
    """_fetch_master returns body.splitlines()."""
    completed = _stub_run()
    completed.stdout = _gh_view_body_payload("1. #1307\n2. §6.18\n")
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=completed,
    ):
        lines = _fetch_master(1)
    assert lines == ["1. #1307", "2. §6.18"]


def _run_fetch_master_with_failure(
    capsys: pytest.CaptureFixture[str],
) -> tuple[int | str | None, str]:
    """Run _fetch_master against a failing gh stub; return (exit_code, stderr)."""
    completed = _stub_run(returncode=1)
    completed.stdout = ""
    completed.stderr = "gh: boom"
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=completed,
    ):
        with pytest.raises(SystemExit) as excinfo:
            _fetch_master(1)
    return excinfo.value.code, capsys.readouterr().err


def test_fetch_master_exits_with_gh_returncode(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A non-zero gh propagates its returncode via SystemExit."""
    rc, _err = _run_fetch_master_with_failure(capsys)
    assert rc == 1


def test_fetch_master_prints_gh_stderr_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A failing gh's stderr is forwarded to our stderr before exit."""
    _rc, err = _run_fetch_master_with_failure(capsys)
    assert "gh: boom" in err


def _run_fetch_master_happy(
    capsys: pytest.CaptureFixture[str],
) -> tuple[str, str]:
    """Run _fetch_master against a successful gh stub; return (stdout, stderr)."""
    completed = _stub_run()
    completed.stdout = _gh_view_body_payload("1. #1307\n")
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=completed,
    ):
        _fetch_master(1)
    captured = capsys.readouterr()
    return captured.out, captured.err


def test_fetch_master_announces_on_stdout(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """_fetch_master prints its banner to stdout."""
    out, _err = _run_fetch_master_happy(capsys)
    assert "issue #1" in out


def test_fetch_master_does_not_write_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """_fetch_master must not touch stderr on the happy path."""
    _out, err = _run_fetch_master_happy(capsys)
    assert err == ""


# --- _fetch_linked_issue ----------------------------------------------------


def _gh_view_state_title_payload(state: str, title: str) -> str:
    """Build a `gh issue view --json state,title` payload."""
    return json.dumps({"state": state, "title": title})


def test_fetch_linked_issue_returns_state_and_title() -> None:
    """_fetch_linked_issue returns (state_upper, title)."""
    completed = _stub_run()
    completed.stdout = _gh_view_state_title_payload(
        "OPEN", "Satisfy IEEE 1800-2023 §6.18",
    )
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=completed,
    ):
        result = _fetch_linked_issue(1307)
    assert result == ("OPEN", "Satisfy IEEE 1800-2023 §6.18")


def _run_fetch_linked_issue_failing(rc: int) -> int | str | None:
    """Run _fetch_linked_issue against a failing gh; return the SystemExit code."""
    completed = _stub_run(returncode=rc)
    completed.stdout = ""
    completed.stderr = "gh: nope"
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=completed,
    ):
        with pytest.raises(SystemExit) as excinfo:
            _fetch_linked_issue(1307)
    return excinfo.value.code


def test_fetch_linked_issue_exits_with_gh_returncode() -> None:
    """A non-zero gh propagates its returncode via SystemExit."""
    assert _run_fetch_linked_issue_failing(5) == 5


# --- _resolve_linked --------------------------------------------------------


def _patch_fetch_linked(
    *, state: str, title: str,
) -> Any:
    """Patch _fetch_linked_issue with a fixed (state, title)."""
    return patch(
        "satisfy_subclauses.pipeline._fetch_linked_issue",
        return_value=(state, title),
    )


def test_resolve_linked_open_canonical_returns_subclause() -> None:
    """OPEN canonical title yields the subclause."""
    with _patch_fetch_linked(
        state="OPEN", title="Satisfy IEEE 1800-2023 §6.18",
    ):
        assert _resolve_linked(1307, line_index=1) == "6.18"


def test_resolve_linked_open_legacy_audit_numeric_returns_subclause() -> None:
    """OPEN legacy audit-numeric title yields the subclause."""
    title = (
        "Ensure IEEE 1800-2023 §6.18 functionalities and tests are"
        " implemented and properly named"
    )
    with _patch_fetch_linked(state="OPEN", title=title):
        assert _resolve_linked(1307, line_index=1) == "6.18"


def test_resolve_linked_open_legacy_audit_annex_returns_subclause() -> None:
    """OPEN legacy audit-annex (no §) title yields the annex subclause."""
    title = (
        "Ensure IEEE 1800-2023 A.6.7 functionalities and tests are"
        " implemented and properly named"
    )
    with _patch_fetch_linked(state="OPEN", title=title):
        assert _resolve_linked(609, line_index=1) == "A.6.7"


def test_resolve_linked_closed_returns_none() -> None:
    """CLOSED returns None and does not raise."""
    with _patch_fetch_linked(
        state="CLOSED", title="Satisfy IEEE 1800-2023 §6.18",
    ):
        assert _resolve_linked(1307, line_index=4) is None


def _run_resolve_linked_closed(
    capsys: pytest.CaptureFixture[str],
) -> tuple[str, str]:
    """Run _resolve_linked on a closed sub-issue; return (stdout, stderr)."""
    with _patch_fetch_linked(
        state="CLOSED", title="Satisfy IEEE 1800-2023 §6.18",
    ):
        _resolve_linked(1307, line_index=4)
    captured = capsys.readouterr()
    return captured.out, captured.err


def test_resolve_linked_closed_prints_skip_to_stdout(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """CLOSED prints a skip line to stdout naming the issue and line."""
    out, _err = _run_resolve_linked_closed(capsys)
    assert "skipping closed sub-issue #1307" in out and "line 4" in out


def test_resolve_linked_closed_does_not_write_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """The CLOSED skip path must not touch stderr."""
    _out, err = _run_resolve_linked_closed(capsys)
    assert err == ""


def _run_resolve_linked_open_garbage() -> str:
    """Trigger the unparseable-title RuntimeError; return the message."""
    with _patch_fetch_linked(state="OPEN", title="totally unrelated"):
        with pytest.raises(RuntimeError) as excinfo:
            _resolve_linked(1307, line_index=4)
    return str(excinfo.value)


def test_resolve_linked_open_unparseable_title_raises() -> None:
    """OPEN issue with no recognised subclause shape raises with issue and title named."""
    msg = _run_resolve_linked_open_garbage()
    assert "#1307" in msg and "totally unrelated" in msg


# --- _patch_master_body -----------------------------------------------------


def _run_patch_master_body() -> MagicMock:
    """Run _patch_master_body against a stubbed gh; return the mock."""
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=_stub_run(),
    ) as mock_run:
        _patch_master_body(1, "new body\n")
    return mock_run


def test_patch_master_body_invokes_gh_issue_edit() -> None:
    """The argv targets gh issue edit on the master issue number."""
    argv = _run_patch_master_body().call_args.args[0]
    assert argv[:4] == ["gh", "issue", "edit", "1"]


def test_patch_master_body_uses_body_file_flag() -> None:
    """The argv passes --body-file to stream the new body."""
    argv = _run_patch_master_body().call_args.args[0]
    assert "--body-file" in argv


def test_patch_master_body_sends_body_on_stdin() -> None:
    """The body string is forwarded on subprocess.run's stdin."""
    mock_run = _run_patch_master_body()
    assert mock_run.call_args.kwargs["input"] == "new body\n"


def _run_patch_master_body_failure(
    capsys: pytest.CaptureFixture[str],
) -> tuple[int | str | None, str]:
    """Run _patch_master_body against a failing gh; return (exit_code, stderr)."""
    completed = _stub_run(returncode=3)
    completed.stderr = "edit failed"
    with patch(
        "satisfy_subclauses.pipeline.subprocess.run",
        return_value=completed,
    ):
        with pytest.raises(SystemExit) as excinfo:
            _patch_master_body(1, "body")
    return excinfo.value.code, capsys.readouterr().err


def test_patch_master_body_exits_with_gh_returncode(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A non-zero gh propagates its returncode via SystemExit."""
    rc, _err = _run_patch_master_body_failure(capsys)
    assert rc == 3


def test_patch_master_body_prints_gh_stderr_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A failing gh's stderr is forwarded to our stderr before exit."""
    _rc, err = _run_patch_master_body_failure(capsys)
    assert "edit failed" in err


# --- _resolve_unlinked ------------------------------------------------------


def test_resolve_unlinked_mutates_body_line_in_place() -> None:
    """_resolve_unlinked swaps §X.Y for #NNN on the named line; others untouched."""
    body_lines = ["1. #1307", "2. §6.18", "3. §A.7"]
    with patch(
        "satisfy_subclauses.pipeline.find_or_create_issue", return_value=(5000, "OPEN"),
    ):
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            _resolve_unlinked(
                1, "6.18",
                master_issue=1, body_lines=body_lines, labels=_LABELS,
            )
    assert body_lines == ["1. #1307", "2. #5000", "3. §A.7"]


def test_resolve_unlinked_patches_master_body_with_updated_lines() -> None:
    """_resolve_unlinked calls _patch_master_body with the joined updated body."""
    body_lines = ["1. §6.18", "2. §A.7"]
    with patch(
        "satisfy_subclauses.pipeline.find_or_create_issue", return_value=(42, "OPEN"),
    ):
        with patch(
            "satisfy_subclauses.pipeline._patch_master_body",
        ) as mock_patch:
            _resolve_unlinked(
                0, "6.18",
                master_issue=99, body_lines=body_lines, labels=_LABELS,
            )
    assert mock_patch.call_args.args == (99, "1. #42\n2. §A.7")


def test_resolve_unlinked_returns_subclause() -> None:
    """_resolve_unlinked returns the input subclause."""
    body_lines = ["1. §6.18"]
    with patch(
        "satisfy_subclauses.pipeline.find_or_create_issue", return_value=(42, "OPEN"),
    ):
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            result = _resolve_unlinked(
                0, "6.18",
                master_issue=1, body_lines=body_lines, labels=_LABELS,
            )
    assert result == "6.18"


def _run_resolve_unlinked_capturing(
    capsys: pytest.CaptureFixture[str],
) -> tuple[str, str]:
    """Run _resolve_unlinked with all gh dependencies stubbed; return capsys."""
    body_lines = ["1. §6.18"]
    with patch(
        "satisfy_subclauses.pipeline.find_or_create_issue", return_value=(42, "OPEN"),
    ):
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            _resolve_unlinked(
                0, "6.18",
                master_issue=1, body_lines=body_lines, labels=_LABELS,
            )
    captured = capsys.readouterr()
    return captured.out, captured.err


def test_resolve_unlinked_announces_link_on_stdout(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """_resolve_unlinked announces the §X.Y → #NNN link on stdout."""
    out, _err = _run_resolve_unlinked_capturing(capsys)
    assert "§6.18" in out and "#42" in out


def test_resolve_unlinked_does_not_write_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """_resolve_unlinked must not touch stderr on the happy path."""
    _out, err = _run_resolve_unlinked_capturing(capsys)
    assert err == ""


# --- satisfy_subclauses_from_issue -----------------------------------------


def _stub_from_issue(
    body: str, linked_states: dict[int, tuple[str, str]],
) -> tuple[Any, Any, Any, Any]:
    """Patch the integration points for the end-to-end driver.

    Returns (patch_fetch_master, patch_fetch_linked, patch_find_or_create,
    patch_subprocess_run).
    """

    def fake_fetch_master(_issue: int) -> list[str]:
        return body.splitlines()

    def fake_fetch_linked(num: int) -> tuple[str, str]:
        return linked_states[num]

    return (
        patch(
            "satisfy_subclauses.pipeline._fetch_master",
            side_effect=fake_fetch_master,
        ),
        patch(
            "satisfy_subclauses.pipeline._fetch_linked_issue",
            side_effect=fake_fetch_linked,
        ),
        patch(
            "satisfy_subclauses.pipeline.find_or_create_issue",
            return_value=(5000, "OPEN"),
        ),
        patch(
            "satisfy_subclauses.pipeline.subprocess.run",
            return_value=_stub_run(),
        ),
    )


def _collect_subclause_args(mock_run: MagicMock) -> list[str]:
    """Return the --subclause value from each captured subprocess call."""
    return [
        c.args[0][c.args[0].index("--subclause") + 1]
        for c in mock_run.call_args_list
        if "--subclause" in c.args[0]
    ]


def test_from_issue_dispatches_open_hash_via_subprocess() -> None:
    """An OPEN #NNN entry dispatches satisfy_subclause for the parsed subclause."""
    body = "1. #1307\n"
    pm, pl, _pf, ps = _stub_from_issue(
        body, {1307: ("OPEN", "Satisfy IEEE 1800-2023 §6.18")},
    )
    with pm, pl, _pf, ps as mock_run:
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            satisfy_subclauses_from_issue(
                1, _LRM, model="opus", labels=_LABELS,
            )
    assert _collect_subclause_args(mock_run) == ["6.18"]


def test_from_issue_skips_closed_hash() -> None:
    """A CLOSED #NNN entry is not dispatched."""
    body = "1. #1307\n"
    pm, pl, _pf, ps = _stub_from_issue(
        body, {1307: ("CLOSED", "Satisfy IEEE 1800-2023 §6.18")},
    )
    with pm, pl, _pf, ps as mock_run:
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            satisfy_subclauses_from_issue(
                1, _LRM, model="opus", labels=_LABELS,
            )
    assert _collect_subclause_args(mock_run) == []


def _run_from_issue_section_only() -> tuple[MagicMock, MagicMock]:
    """Run satisfy_subclauses_from_issue on a single §X.Y entry; return mocks."""
    body = "1. §6.18\n"
    pm, pl, pf, ps = _stub_from_issue(body, {})
    with pm, pl, pf, ps as mock_run:
        with patch(
            "satisfy_subclauses.pipeline._patch_master_body",
        ) as mock_patch:
            satisfy_subclauses_from_issue(
                1, _LRM, model="opus", labels=_LABELS,
            )
    return mock_run, mock_patch


def test_from_issue_section_marker_dispatches_subprocess() -> None:
    """A §X.Y entry dispatches satisfy_subclause for the captured subclause."""
    mock_run, _mock_patch = _run_from_issue_section_only()
    assert _collect_subclause_args(mock_run) == ["6.18"]


def test_from_issue_section_marker_patches_master_body() -> None:
    """A §X.Y entry triggers a master-body PATCH."""
    _mock_run, mock_patch = _run_from_issue_section_only()
    assert mock_patch.called


def test_from_issue_section_patch_runs_before_subprocess() -> None:
    """The master-body PATCH must precede the satisfy_subclause subprocess."""
    body = "1. §6.18\n"
    pm, pl, pf, _ps = _stub_from_issue(body, {})

    order: list[str] = []

    def patch_recorder(_master: int, _body: str) -> None:
        order.append("patch")

    def run_recorder(*_a: object, **_k: object) -> MagicMock:
        order.append("run")
        return _stub_run()

    with pm, pl, pf:
        with patch(
            "satisfy_subclauses.pipeline._patch_master_body",
            side_effect=patch_recorder,
        ):
            with patch(
                "satisfy_subclauses.pipeline.subprocess.run",
                side_effect=run_recorder,
            ):
                satisfy_subclauses_from_issue(
                    1, _LRM, model="opus", labels=_LABELS,
                )
    assert order == ["patch", "run"]


def test_from_issue_preserves_order_and_skips_closed_links() -> None:
    """Mixed body: closed hash → skip, open hash → dispatch, §X.Y → resolve+dispatch."""
    body = "1. #1300\n2. #1307\n3. §6.18\n"
    linked = {
        1300: ("CLOSED", "Satisfy IEEE 1800-2023 §3.9"),
        1307: ("OPEN", "Satisfy IEEE 1800-2023 §6.19"),
    }
    pm, pl, pf, ps = _stub_from_issue(body, linked)
    with pm, pl, pf, ps as mock_run:
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            satisfy_subclauses_from_issue(
                1, _LRM, model="opus", labels=_LABELS,
            )
    assert _collect_subclause_args(mock_run) == ["6.19", "6.18"]


def _run_from_issue_with_body(
    body: str, linked_states: dict[int, tuple[str, str]] | None = None,
) -> None:
    """Run satisfy_subclauses_from_issue with the integration points stubbed."""
    pm, pl, pf, ps = _stub_from_issue(body, linked_states or {})
    with pm, pl, pf, ps:
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            satisfy_subclauses_from_issue(
                1, _LRM, model="opus", labels=_LABELS,
            )


def test_from_issue_announces_start_to_stdout(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """satisfy_subclauses_from_issue prints a start-of-run banner on stdout."""
    _run_from_issue_with_body("")
    captured = capsys.readouterr()
    assert "--issue 1" in captured.out


def test_from_issue_happy_path_does_not_write_to_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """The happy path keeps stderr empty (stderr is reserved for errors)."""
    _run_from_issue_with_body("")
    assert capsys.readouterr().err == ""


def test_from_issue_warns_on_non_entry_line_to_stdout(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """A non-entry, non-blank line prints a loud-ignore line on stdout."""
    body = "1. #1307\nsome stray free text\n2. §6.18\n"
    linked = {1307: ("OPEN", "Satisfy IEEE 1800-2023 §6.19")}
    _run_from_issue_with_body(body, linked)
    captured = capsys.readouterr()
    assert "ignoring non-entry line" in captured.out and "stray free text" in captured.out


def test_from_issue_blank_lines_are_quietly_skipped(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Blank lines are skipped with no announcement (the one tolerated non-entry)."""
    body = "1. #1307\n\n2. §6.18\n"
    linked = {1307: ("OPEN", "Satisfy IEEE 1800-2023 §6.19")}
    _run_from_issue_with_body(body, linked)
    assert "ignoring non-entry line" not in capsys.readouterr().out


def test_from_issue_empty_body_runs_no_dispatch() -> None:
    """An empty body produces no satisfy_subclause subprocess calls."""
    pm, pl, pf, ps = _stub_from_issue("", {})
    with pm, pl, pf, ps as mock_run:
        with patch("satisfy_subclauses.pipeline._patch_master_body"):
            satisfy_subclauses_from_issue(
                1, _LRM, model="opus", labels=_LABELS,
            )
    assert _collect_subclause_args(mock_run) == []
