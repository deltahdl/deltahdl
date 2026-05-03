"""Unit tests for classification functions in classify_test."""

import json
import subprocess
import time
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any, cast
from unittest.mock import MagicMock

import pytest

from classify_test._patterns import CLAUSE_PROMPT_TEMPLATE


def _multi_claude(
    clause_resp: dict[str, Any], prefix_stage: str = "parser",
) -> Callable[..., dict[str, Any]]:
    """Return a mock _call_claude that handles clause and prefix calls."""
    def _mock(
        _prompt: str, schema: str | None = None, **_kw: Any,
    ) -> dict[str, Any]:
        if schema and "pipeline_stage" in schema:
            return {"pipeline_stage": prefix_stage, "rationale": "r"}
        return clause_resp
    return _mock


# ---- existing_non_lrm_topics ----------------------------------------------


def test_existing_non_lrm_topics_empty(ct: ModuleType, tmp_path: Path) -> None:
    """Returns [] when no matching files exist."""
    assert ct.existing_non_lrm_topics(tmp_path) == []


def test_existing_non_lrm_topics_simple(ct: ModuleType, tmp_path: Path) -> None:
    """Returns topic name without letter suffix."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == ["aig"]


def test_existing_non_lrm_topics_letter_suffix(ct: ModuleType, tmp_path: Path) -> None:
    """Strips single letter suffix (e.g., _a) from topic."""
    (tmp_path / "test_non_lrm_arena_a.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == ["arena"]


def test_existing_non_lrm_topics_short_topic(ct: ModuleType, tmp_path: Path) -> None:
    """Short topic (1 char) does not trigger suffix stripping."""
    (tmp_path / "test_non_lrm_x.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == ["x"]


def test_existing_non_lrm_topics_empty_topic(ct: ModuleType, tmp_path: Path) -> None:
    """File whose stem after prefix is empty is skipped."""
    (tmp_path / "test_non_lrm_.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == []


# ---- _detect_prefix --------------------------------------------------------


def _stub_prefix_claude(monkeypatch: pytest.MonkeyPatch, ct: ModuleType, stage: str) -> None:
    """Stub _call_claude to return the given pipeline stage."""
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda _p, _s=None, **_kw: {
            "pipeline_stage": stage, "rationale": "r",
        },
    )


def test_detect_prefix_returns_claude_stage(ct: ModuleType, ct_helpers: ModuleType,
                                            monkeypatch: pytest.MonkeyPatch) -> None:
    """Returns prefix based on Claude's pipeline_stage response."""
    _stub_prefix_claude(monkeypatch, ct, "parser")
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    assert getattr(ct, "_detect_prefix")(t, "6.1", "/lrm") == "test_parser_"


def test_detect_prefix_non_lrm_override(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Non-LRM clause overrides to test_non_lrm_ without calling Claude."""
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    assert getattr(ct, "_detect_prefix")(t, "non-lrm", "/lrm") == "test_non_lrm_"


def test_detect_prefix_non_lrm_underscore(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Non_lrm (underscore variant) also overrides prefix."""
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    assert getattr(ct, "_detect_prefix")(t, "non_lrm", "/lrm") == "test_non_lrm_"


def test_detect_prefix_stores_rationale(ct: ModuleType, ct_helpers: ModuleType,
                                        monkeypatch: pytest.MonkeyPatch) -> None:
    """Stores Claude's rationale on the test block."""
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda _p, _s=None, **_kw: {
            "pipeline_stage": "simulator", "rationale": "timing checks",
        },
    )
    t = ct_helpers.make_test_block("T", body=["  x();"])
    getattr(ct, "_detect_prefix")(t, "6.1", "/lrm")
    assert t.classification.prefix_rationale == "timing checks"


def test_detect_prefix_calls_claude(ct: ModuleType, ct_helpers: ModuleType,
                                    monkeypatch: pytest.MonkeyPatch) -> None:
    """Invokes _call_claude with prefix prompt."""
    calls: list[str] = []

    def spy(
        prompt: str, _schema: str | None = None, **_kw: Any,
    ) -> dict[str, Any]:
        calls.append(prompt)
        return {"pipeline_stage": "simulator", "rationale": "r"}

    monkeypatch.setattr(ct, "_call_claude", spy)
    t = ct_helpers.make_test_block("T", body=["  x();"])
    getattr(ct, "_detect_prefix")(t, "6.1", "/lrm")
    assert "pipeline stage" in calls[0].lower()


def test_detect_prefix_invalid_stage_exits(ct: ModuleType, ct_helpers: ModuleType,
                                           monkeypatch: pytest.MonkeyPatch) -> None:
    """Exits when Claude returns an unrecognized pipeline stage."""
    _stub_prefix_claude(monkeypatch, ct, "bogus")
    t = ct_helpers.make_test_block("T", body=["  x();"])
    with pytest.raises(SystemExit):
        getattr(ct, "_detect_prefix")(t, "6.1", "/lrm")


# ---- _build_clause_prompt --------------------------------------------------


def test_build_clause_prompt_contains_lrm_path(ct: ModuleType, ct_helpers: ModuleType,
                                               tmp_path: Path) -> None:
    """Clause prompt includes the LRM file path."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = ct.build_clause_prompt
    lrm = tmp_path / "LRM.txt"
    t = _tb("X")
    prompt = _build_clause_prompt(t, lrm)
    assert str(lrm) in prompt


def test_build_clause_prompt_contains_test_body(ct: ModuleType, ct_helpers: ModuleType,
                                                tmp_path: Path) -> None:
    """Clause prompt includes the test's source code."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = ct.build_clause_prompt
    t = _tb("MyTest")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "TEST(S, MyTest)" in prompt


def test_build_clause_prompt_no_prefix_instructions(ct: ModuleType, ct_helpers: ModuleType,
                                                    tmp_path: Path) -> None:
    """Clause prompt does not mention pipeline prefixes."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = ct.build_clause_prompt
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "test_parser_" not in prompt


def test_build_clause_prompt_no_arch_path(
    ct: ModuleType, ct_helpers: ModuleType, tmp_path: Path,
) -> None:
    """Clause prompt does not reference architecture file."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = ct.build_clause_prompt
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "architecture" not in prompt.lower()


def test_build_clause_prompt_no_file_context(
    ct: ModuleType, ct_helpers: ModuleType, tmp_path: Path,
) -> None:
    """Clause prompt does not include FILE CONTEXT."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = ct.build_clause_prompt
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "FILE CONTEXT" not in prompt


# ---- _build_topic_prompt ---------------------------------------------------


def test_build_topic_prompt_no_topics(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Topic prompt without existing topics omits hint."""
    t = ct_helpers.make_test_block("X")
    prompt = ct.build_topic_prompt(t, "")
    assert "Existing topic files" not in prompt


def test_build_topic_prompt_with_topics(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Topic prompt with existing topics includes hint."""
    t = ct_helpers.make_test_block("X")
    prompt = ct.build_topic_prompt(t, "Existing topic files: aig\n")
    assert "Existing topic files" in prompt


def test_build_topic_prompt_contains_test_body(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Topic prompt includes the test's source code."""
    t = ct_helpers.make_test_block("MyTest")
    prompt = ct.build_topic_prompt(t, "")
    assert "TEST(S, MyTest)" in prompt


# ---- _extract_json ---------------------------------------------------------


def test_extract_json_direct(ct: ModuleType) -> None:
    """Parses clean JSON directly."""
    _extract_json = getattr(ct, "_extract_json")
    assert _extract_json('{"a": 1}') == {"a": 1}


def test_extract_json_embedded(ct: ModuleType) -> None:
    """Extracts JSON embedded in surrounding text."""
    _extract_json = getattr(ct, "_extract_json")
    text = 'Here is the answer: {"a": 1} done.'
    assert _extract_json(text) == {"a": 1}


def test_extract_json_invalid(ct: ModuleType) -> None:
    """Exits when no valid JSON can be extracted."""
    _extract_json = getattr(ct, "_extract_json")
    with pytest.raises(SystemExit):
        _extract_json("no json here")


def test_extract_json_embedded_invalid(ct: ModuleType) -> None:
    """Exits when embedded braces contain invalid JSON."""
    _extract_json = getattr(ct, "_extract_json")
    with pytest.raises(SystemExit):
        _extract_json("prefix {not json} suffix")


# ---- _call_claude ----------------------------------------------------------


def test_call_claude_success(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """Returns parsed JSON from --output-format json envelope."""
    _call_claude = getattr(ct, "_call_claude")
    inner = '{"clause": "6.1", "rationale": "r"}'
    envelope = json.dumps({"result": inner, "session_id": "x"})
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = envelope
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"clause": "6.1", "rationale": "r"}


def test_call_claude_raw_text_fallback(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """Falls back to _extract_json when stdout is not valid JSON."""
    _call_claude = getattr(ct, "_call_claude")
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = 'Here is the answer: {"clause": "6.1"}'
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"clause": "6.1"}


def test_call_claude_structured_output(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """Returns structured_output directly when present in envelope."""
    _call_claude = getattr(ct, "_call_claude")
    envelope = json.dumps({
        "result": "",
        "structured_output": {"clause": "25.7", "rationale": "r"},
        "session_id": "x",
    })
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = envelope
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"clause": "25.7", "rationale": "r"}


def test_call_claude_failure(ct: ModuleType, ct_helpers: ModuleType,
                             monkeypatch: pytest.MonkeyPatch) -> None:
    """Exits on non-zero return code."""
    _call_claude = getattr(ct, "_call_claude")
    ct_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        _call_claude("prompt")


def _capture_claude_cmd(ct: ModuleType, monkeypatch: pytest.MonkeyPatch, schema: str | None = None,
                        continue_session: bool = False) -> list[str]:
    """Run _call_claude and return the captured subprocess command."""
    _call_claude = getattr(ct, "_call_claude")
    captured_cmd: list[str] = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = '{"clause": "6.1", "rationale": "r"}'
    mock_result.stderr = ""

    def capture_run(*args: Any, **_kwargs: Any) -> MagicMock:
        captured_cmd.extend(args[0])
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    _call_claude("prompt", schema=schema,
                 continue_session=continue_session)
    return captured_cmd


def test_call_claude_uses_opus(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """CLI command includes --model opus."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    idx = cmd.index("--model")
    assert cmd[idx + 1] == "opus"


def test_call_claude_omits_effort_flag(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """CLI command does not include --effort."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--effort" not in cmd


def test_call_claude_output_format_json(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """CLI command includes --output-format json."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    idx = cmd.index("--output-format")
    assert cmd[idx + 1] == "json"


def test_call_claude_uses_dangerously_skip_permissions(ct: ModuleType,
                                                       monkeypatch: pytest.MonkeyPatch) -> None:
    """CLI command includes --dangerously-skip-permissions."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--dangerously-skip-permissions" in cmd


def test_call_claude_json_schema(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """CLI command includes --json-schema when schema is provided."""
    schema = '{"type": "object"}'
    cmd = _capture_claude_cmd(ct, monkeypatch, schema=schema)
    idx = cmd.index("--json-schema")
    assert cmd[idx + 1] == schema


def test_call_claude_no_json_schema_by_default(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """CLI command omits --json-schema when no schema is provided."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--json-schema" not in cmd


def test_call_claude_no_continue_by_default(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """CLI command omits --continue by default."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--continue" not in cmd


def test_call_claude_with_continue(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """CLI command includes --continue when continue_session=True."""
    cmd = _capture_claude_cmd(ct, monkeypatch, continue_session=True)
    assert "--continue" in cmd


def test_call_claude_timeout_retries_then_succeeds(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Retries on timeout and returns result on subsequent success."""
    _call_claude = getattr(ct, "_call_claude")
    monkeypatch.setattr(time, "sleep", lambda _s: None)
    mock_ok = MagicMock()
    mock_ok.returncode = 0
    mock_ok.stdout = '{"clause": "6.1", "rationale": "r"}'
    mock_ok.stderr = ""
    calls: list[int] = []

    def run_side_effect(*args: Any, **kwargs: Any) -> MagicMock:
        calls.append(1)
        if len(calls) == 1:
            raise subprocess.TimeoutExpired(
                args[0], cast(float, kwargs.get("timeout")),
            )
        return mock_ok

    monkeypatch.setattr(subprocess, "run", run_side_effect)
    assert _call_claude("prompt") == {"clause": "6.1", "rationale": "r"}


def test_call_claude_timeout_exhausted(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """Exits after all retry attempts are exhausted by timeouts."""
    _call_claude = getattr(ct, "_call_claude")
    monkeypatch.setattr(time, "sleep", lambda _s: None)

    def run_timeout(*args: Any, **kwargs: Any) -> MagicMock:
        raise subprocess.TimeoutExpired(
            args[0], cast(float, kwargs.get("timeout")),
        )

    monkeypatch.setattr(subprocess, "run", run_timeout)
    with pytest.raises(SystemExit):
        _call_claude("prompt")


def test_call_claude_failure_retries_then_succeeds(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Retries on non-zero exit code and returns result on success."""
    _call_claude = getattr(ct, "_call_claude")
    monkeypatch.setattr(time, "sleep", lambda _s: None)
    mock_fail = MagicMock()
    mock_fail.returncode = 1
    mock_fail.stdout = ""
    mock_fail.stderr = "error"
    mock_ok = MagicMock()
    mock_ok.returncode = 0
    mock_ok.stdout = '{"clause": "6.1", "rationale": "r"}'
    mock_ok.stderr = ""
    calls: list[int] = []

    def run_side_effect(*_args: Any, **_kwargs: Any) -> MagicMock:
        calls.append(1)
        if len(calls) == 1:
            return mock_fail
        return mock_ok

    monkeypatch.setattr(subprocess, "run", run_side_effect)
    assert _call_claude("prompt") == {"clause": "6.1", "rationale": "r"}


def test_call_claude_failure_exhausted(ct: ModuleType, monkeypatch: pytest.MonkeyPatch) -> None:
    """Exits after all retry attempts are exhausted by failures."""
    _call_claude = getattr(ct, "_call_claude")
    monkeypatch.setattr(time, "sleep", lambda _s: None)
    mock_fail = MagicMock()
    mock_fail.returncode = 1
    mock_fail.stdout = ""
    mock_fail.stderr = "error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_fail,
    )
    with pytest.raises(SystemExit):
        _call_claude("prompt")


# ---- _apply_classification -------------------------------------------------


def test_apply_classification_found(ct: ModuleType, ct_helpers: ModuleType,
                                    monkeypatch: pytest.MonkeyPatch) -> None:
    """Applies prefix, clause, and rationale from clause response."""
    _stub_prefix_claude(monkeypatch, ct, "parser")
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("MyTest", body=["  auto r = Parse(src);"])
    clause_resp = {
        "clause": "6.1", "rationale": "reason",
        "suite_name": "Parsing", "test_name": "MyTest",
    }
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.classification.prefix == "test_parser_" and t.classification.clause == "6.1"


def test_apply_classification_non_lrm_underscore(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Normalizes non_lrm to non-lrm."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non_lrm", "rationale": "r",
                   "suite_name": "S", "test_name": "T"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r",
                  "suite_name": "AigGraph", "test_name": "BasicOp"}
    _apply_classification(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    assert t.classification.clause == "non-lrm:aig"


def _apply_non_lrm_aig(ct: ModuleType, ct_helpers: ModuleType) -> Any:
    """Apply non-lrm classification with aig topic, return test block."""
    apply_fn = getattr(ct, "_apply_classification")
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non-lrm", "rationale": "r",
                   "suite_name": "S", "test_name": "T"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r",
                  "suite_name": "AigGraph", "test_name": "BasicOp"}
    apply_fn(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    return t


def test_apply_classification_non_lrm_with_topic(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """Appends topic to non-lrm clause."""
    t = _apply_non_lrm_aig(ct, ct_helpers)
    assert t.classification.clause == "non-lrm:aig"


def test_apply_classification_no_rationale(ct: ModuleType, ct_helpers: ModuleType,
                                           monkeypatch: pytest.MonkeyPatch) -> None:
    """Missing rationale defaults to empty string."""
    _stub_prefix_claude(monkeypatch, ct, "parser")
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "6.1", "suite_name": "S", "test_name": "T"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.classification.rationale == ""


def test_apply_classification_non_lrm_empty_topic(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """non-lrm clause with empty topic causes SystemExit."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non-lrm", "rationale": "r",
                   "suite_name": "S", "test_name": "T"}
    topic_resp = {"non_lrm_topic": "", "rationale": "r",
                  "suite_name": "S", "test_name": "T"}
    with pytest.raises(SystemExit):
        _apply_classification(
            t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt",
        )


def test_apply_classification_detects_prefix(ct: ModuleType, ct_helpers: ModuleType,
                                             monkeypatch: pytest.MonkeyPatch) -> None:
    """Prefix is derived from Claude's pipeline stage detection."""
    _stub_prefix_claude(monkeypatch, ct, "elaborator")
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto* d = Elaborate(src);"])
    clause_resp = {"clause": "6.1", "rationale": "r",
                   "suite_name": "Elaboration", "test_name": "T"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.classification.prefix == "test_elaborator_"


def test_apply_classification_non_lrm_prefix_override(
    ct: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Non-LRM clause overrides prefix to test_non_lrm_."""
    t = _apply_non_lrm_aig(ct, ct_helpers)
    assert t.classification.prefix == "test_non_lrm_"


# ---- classify_test_block ----------------------------------------------------


def _run_against(ct: ModuleType, ct_helpers: ModuleType, monkeypatch: pytest.MonkeyPatch,
                 tmp_path: Path, clause: str) -> tuple[Any, Any]:
    """Classify with --against and return result."""
    monkeypatch.setattr(
        ct, "_call_claude",
        _multi_claude({"clause": clause, "rationale": "r",
                       "suite_name": "S", "test_name": "T"}),
    )
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    return ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt", against="23.2.1",
    ), t


def test_classify_block_against_none_returns_none(
    ct: ModuleType,
    ct_helpers: ModuleType,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """classify_test_block returns None when against clause is 'none'."""
    result, _ = _run_against(ct, ct_helpers, monkeypatch, tmp_path, "none")
    assert result is None


def test_classify_block_against_match_returns_test(
    ct: ModuleType,
    ct_helpers: ModuleType,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """classify_test_block returns test when against clause matches."""
    result, t = _run_against(ct, ct_helpers, monkeypatch, tmp_path, "23.2.1")
    assert result is t


def test_classify_block_against_uses_against_template(ct: ModuleType, ct_helpers: ModuleType,
                                                      monkeypatch: pytest.MonkeyPatch,
                                                      tmp_path: Path) -> None:
    """classify_test_block uses the against prompt template."""
    prompts: list[str] = []

    def capturing(
        prompt: str, schema: str | None = None, **_kw: Any,
    ) -> dict[str, Any]:
        prompts.append(prompt)
        if schema and "pipeline_stage" in schema:
            return {"pipeline_stage": "parser", "rationale": "r"}
        return {"clause": "23.2.1", "rationale": "r",
                "suite_name": "S", "test_name": "T"}

    monkeypatch.setattr(ct, "_call_claude", capturing)
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt", against="23.2.1",
    )
    assert "23.2.1" in prompts[0]


def test_classify_tests_matching(ct: ModuleType, ct_helpers: ModuleType,
                                 monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """classify_test_block applies classification per test."""
    _tb = ct_helpers.make_test_block
    clause_resp = {"clause": "6.1", "rationale": "r",
                   "suite_name": "Parsing", "test_name": "T"}
    monkeypatch.setattr(ct, "_call_claude", _multi_claude(clause_resp))
    t = _tb("T", body=["  auto r = Parse(src);"])
    ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt",
    )
    assert t.classification.prefix == "test_parser_"


def _do_non_lrm_two_calls(ct: ModuleType, ct_helpers: ModuleType, monkeypatch: pytest.MonkeyPatch,
                          tmp_path: Path) -> tuple[int, Any]:
    """Classify a non-LRM test and return (call_count, test)."""
    _tb = ct_helpers.make_test_block
    call_count = [0]

    def two_call_claude(
        _prompt: str, _schema: str | None = None, **_kw: Any,
    ) -> dict[str, Any]:
        call_count[0] += 1
        if call_count[0] == 1:
            return {"clause": "non-lrm", "rationale": "r",
                    "suite_name": "S", "test_name": "T"}
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "BasicOp"}

    monkeypatch.setattr(
        ct, "_call_claude", two_call_claude,
    )
    t = _tb("T", body=["  auto r = Parse(src);"])
    ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt",
    )
    return call_count[0], t


def test_classify_tests_non_lrm_call_count(ct: ModuleType, ct_helpers: ModuleType,
                                           monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """classify_tests makes two Claude calls for non-LRM tests."""
    count, _ = _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path)
    assert count == 2


def test_classify_tests_non_lrm_clause(ct: ModuleType, ct_helpers: ModuleType,
                                       monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """classify_tests sets clause to non-lrm:aig for non-LRM tests."""
    _, t = _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path)
    assert t.classification.clause == "non-lrm:aig"


def test_classify_tests_non_lrm_prefix(ct: ModuleType, ct_helpers: ModuleType,
                                       monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    """classify_tests sets prefix to test_non_lrm_ for non-LRM tests."""
    _, t = _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path)
    assert t.classification.prefix == "test_non_lrm_"


# ---- _validate_clause_response helpers -------------------------------------


def _valid_clause(**overrides: Any) -> dict[str, Any]:
    """Build a minimal valid clause response."""
    base: dict[str, Any] = {"clause": "6.1", "rationale": "r",
                            "suite_name": "S", "test_name": "T"}
    base.update(overrides)
    return base


def _valid_topic(**overrides: Any) -> dict[str, Any]:
    """Build a valid topic response."""
    base: dict[str, Any] = {"non_lrm_topic": "aig", "rationale": "r",
                            "suite_name": "S", "test_name": "T"}
    base.update(overrides)
    return base


# ---- _validate_clause_response: required keys ------------------------------


def test_validate_clause_response_missing_clause(ct: ModuleType) -> None:
    """Exits when response is missing the clause key."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response({"rationale": "r"}, "T")


# ---- _validate_clause_response: clause format ------------------------------


def test_validate_clause_response_invalid_clause_letters(ct: ModuleType) -> None:
    """Exits when clause is arbitrary text."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause="abc"), "T")


def test_validate_clause_response_invalid_clause_empty(ct: ModuleType) -> None:
    """Exits when clause is an empty string."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause=""), "T")


def test_validate_clause_response_invalid_clause_trailing_dot(ct: ModuleType) -> None:
    """Exits when clause has a trailing dot."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause="6.1."), "T")


def test_validate_clause_response_clause_single_digit(ct: ModuleType) -> None:
    """Accepts a single-digit clause."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(
        _valid_clause(clause="6"), "T",
    ) is None


def test_validate_clause_response_clause_deep_numeric(ct: ModuleType) -> None:
    """Accepts a deeply nested numeric clause."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(
        _valid_clause(clause="9.2.2.2.2"), "T",
    ) is None


def test_validate_clause_response_clause_annex(ct: ModuleType) -> None:
    """Accepts an annex clause like A.6.3."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(
        _valid_clause(clause="A.6.3"), "T",
    ) is None


def test_validate_clause_response_valid(ct: ModuleType) -> None:
    """Accepts a valid clause response."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(_valid_clause(), "T") is None


def test_validate_clause_response_strips_section_sign(ct: ModuleType) -> None:
    """Strips § prefix from clause value."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    resp = _valid_clause(clause="§28.3")
    _validate_clause_response(resp, "T")
    assert resp["clause"] == "28.3"


# ---- _validate_topic_response ----------------------------------------------


def test_validate_topic_response_missing_topic(ct: ModuleType) -> None:
    """Exits when response has no non_lrm_topic key."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    with pytest.raises(SystemExit):
        _validate_topic_response({"rationale": "r"}, "T")


def test_validate_topic_response_null_topic(ct: ModuleType) -> None:
    """Exits when non_lrm_topic is None."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    with pytest.raises(SystemExit):
        _validate_topic_response(
            _valid_topic(non_lrm_topic=None), "T",
        )


def test_validate_topic_response_empty_topic(ct: ModuleType) -> None:
    """Exits when non_lrm_topic is empty string."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    with pytest.raises(SystemExit):
        _validate_topic_response(_valid_topic(non_lrm_topic=""), "T")


def test_validate_topic_response_valid(ct: ModuleType) -> None:
    """Accepts a valid topic response."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    assert _validate_topic_response(_valid_topic(), "T") is None


# ---- _validate_clause_response: error messages -----------------------------


def test_validate_clause_response_invalid_clause_message(
    ct: ModuleType, capsys: pytest.CaptureFixture[str],
) -> None:
    """Error message contains the invalid clause value."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    try:
        _validate_clause_response(_valid_clause(clause="abc"), "T")
    except SystemExit:
        pass
    assert "abc" in capsys.readouterr().out


def test_validate_topic_response_missing_topic_message(ct: ModuleType,
                                                       capsys: pytest.CaptureFixture[str]) -> None:
    """Error message mentions topic."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    try:
        _validate_topic_response({"rationale": "r"}, "T")
    except SystemExit:
        pass
    assert "topic" in capsys.readouterr().out.lower()


# ---- integration: _apply_classification + validation -----------------------


def test_apply_classification_rejects_bad_clause(ct: ModuleType, ct_helpers: ModuleType) -> None:
    """_apply_classification exits on an invalid clause."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    with pytest.raises(SystemExit):
        _apply_classification(
            t, _valid_clause(clause="abc"), lrm_path="/tmp/lrm.txt",
        )


def test_classify_tests_propagates_validation_error(
    ct: ModuleType,
    ct_helpers: ModuleType,
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """classify_tests exits when Claude returns an invalid clause."""
    _tb = ct_helpers.make_test_block
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda _p, schema=None, **_kw: _valid_clause(clause="abc",
                                                      suite_name="S",
                                                      test_name="T"),
    )
    with pytest.raises(SystemExit):
        ct.classify_test_block(
            _tb("T", body=["  auto r = Parse(src);"]),
            tmp_path, tmp_path / "lrm.txt",
        )


# ---- suite_name / test_name in schema and prompt ---------------------------


def test_clause_schema_has_suite_name(ct: ModuleType) -> None:
    """CLAUSE_SCHEMA includes a suite_name property."""
    schema = json.loads(getattr(ct, "_CLAUSE_SCHEMA"))
    assert "suite_name" in schema["properties"]


def test_clause_schema_has_test_name(ct: ModuleType) -> None:
    """CLAUSE_SCHEMA includes a test_name property."""
    schema = json.loads(getattr(ct, "_CLAUSE_SCHEMA"))
    assert "test_name" in schema["properties"]


def test_clause_prompt_mentions_suite_name() -> None:
    """CLAUSE_PROMPT_TEMPLATE instructs Claude to return a suite name."""
    assert "suite_name" in CLAUSE_PROMPT_TEMPLATE


def test_topic_schema_has_suite_name(ct: ModuleType) -> None:
    """TOPIC_SCHEMA includes a suite_name property."""
    schema = json.loads(getattr(ct, "_TOPIC_SCHEMA"))
    assert "suite_name" in schema["properties"]


def test_topic_schema_has_test_name(ct: ModuleType) -> None:
    """TOPIC_SCHEMA includes a test_name property."""
    schema = json.loads(getattr(ct, "_TOPIC_SCHEMA"))
    assert "test_name" in schema["properties"]


# ---- _apply_classification: renaming ---------------------------------------


def _apply_with_names(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch, *, macro: str = "TEST",
) -> Any:
    """Apply a clause response with suite_name+test_name, return test block."""
    _stub_prefix_claude(monkeypatch, ct, "parser")
    _apply = getattr(ct, "_apply_classification")
    body = ["  auto r = Parse(src);"]
    lines = [f"{macro}(S, MyTest) {{"] + body + ["}"]
    t = ct.TestBlock(
        suite_name="S",
        test_name="MyTest",
        lines=lines,
        preceding_comments=[],
    )
    resp = {
        "clause": "6.1", "rationale": "r",
        "suite_name": "BinaryOps", "test_name": "ParseAddition",
    }
    _apply(t, resp, lrm_path="/tmp/lrm.txt")
    return t


def test_apply_classification_renames_suite(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Updates test.suite_name to the new suite name."""
    assert _apply_with_names(ct, monkeypatch).suite_name == "BinaryOps"


def test_apply_classification_renames_test_name(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Updates test.test_name to the new test name."""
    assert _apply_with_names(ct, monkeypatch).test_name == "ParseAddition"


def test_apply_classification_renames_test_line(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Renames both args in TEST() line."""
    t = _apply_with_names(ct, monkeypatch)
    assert t.lines[0] == "TEST(BinaryOps, ParseAddition) {"


def test_apply_classification_renames_test_f(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Renames both args in TEST_F() line."""
    t = _apply_with_names(ct, monkeypatch, macro="TEST_F")
    assert t.lines[0] == "TEST_F(BinaryOps, ParseAddition) {"


def test_apply_classification_renames_test_p(
    ct: ModuleType, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Renames both args in TEST_P() line."""
    t = _apply_with_names(ct, monkeypatch, macro="TEST_P")
    assert t.lines[0] == "TEST_P(BinaryOps, ParseAddition) {"


def test_rename_preserves_original_test_name(ct: ModuleType) -> None:
    """Second rename keeps the original_test_name from the first rename."""
    _rename = getattr(ct, "_rename_test_macro")
    t = ct.TestBlock(
        suite_name="S", test_name="First",
        lines=["TEST(S, First) {"], preceding_comments=[],
    )
    _rename(t, "A", "Second")
    _rename(t, "B", "Third")
    assert t.classification.original_test_name == "First"
