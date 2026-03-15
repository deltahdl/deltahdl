"""Unit tests for classification functions in classify_test."""

import json
import subprocess
import time
from unittest.mock import MagicMock

import pytest


# ---- existing_non_lrm_topics ----------------------------------------------


def test_existing_non_lrm_topics_empty(ct, tmp_path):
    """Returns [] when no matching files exist."""
    assert ct.existing_non_lrm_topics(tmp_path) == []


def test_existing_non_lrm_topics_simple(ct, tmp_path):
    """Returns topic name without letter suffix."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == ["aig"]


def test_existing_non_lrm_topics_letter_suffix(ct, tmp_path):
    """Strips single letter suffix (e.g., _a) from topic."""
    (tmp_path / "test_non_lrm_arena_a.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == ["arena"]


def test_existing_non_lrm_topics_short_topic(ct, tmp_path):
    """Short topic (1 char) does not trigger suffix stripping."""
    (tmp_path / "test_non_lrm_x.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == ["x"]


def test_existing_non_lrm_topics_empty_topic(ct, tmp_path):
    """File whose stem after prefix is empty is skipped."""
    (tmp_path / "test_non_lrm_.cpp").write_text("")
    assert ct.existing_non_lrm_topics(tmp_path) == []


# ---- _detect_prefix --------------------------------------------------------


def test_detect_prefix_parser(ct, ct_helpers):
    """Detects parser prefix from Parse( call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto r = Parse(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_parser_"


def test_detect_prefix_parser_src(ct, ct_helpers):
    """Detects parser prefix from ParseSrc( variant."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto r = ParseSrc(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_parser_"


def test_detect_prefix_elaborator(ct, ct_helpers):
    """Detects elaborator prefix from Elaborate( call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto* d = Elaborate(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_elaborator_"


def test_detect_prefix_elaborator_src(ct, ct_helpers):
    """Detects elaborator prefix from ElaborateSrc( variant."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto* d = ElaborateSrc(src, f);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_elaborator_"


def test_detect_prefix_lexer_lex(ct, ct_helpers):
    """Detects lexer prefix from Lex( call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto tok = Lex(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_lexer_"


def test_detect_prefix_lexer_one(ct, ct_helpers):
    """Detects lexer prefix from LexOne( variant."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto tok = LexOne(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_lexer_"


def test_detect_prefix_simulator(ct, ct_helpers):
    """Detects simulator prefix from Scheduler( call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  Scheduler sched;"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_simulator_"


def test_detect_prefix_simulator_sim_context(ct, ct_helpers):
    """Detects simulator prefix from SimContext call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  SimContext ctx;"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_simulator_"


def test_detect_prefix_synthesizer(ct, ct_helpers):
    """Detects synthesizer prefix from SynthLower( call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto g = SynthLower(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_synthesizer_"


def test_detect_prefix_synthesizer_aig(ct, ct_helpers):
    """Detects synthesizer prefix from AigGraph."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  AigGraph g;"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_synthesizer_"


def test_detect_prefix_preprocessor(ct, ct_helpers):
    """Detects preprocessor prefix from Preprocessor( call."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  Preprocessor pp(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_preprocessor_"


def test_detect_prefix_non_lrm_override(ct, ct_helpers):
    """Non-LRM clause overrides detected prefix to test_non_lrm_."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto r = Parse(src);"])
    assert _detect_prefix(t, "non-lrm", "/tmp/lrm.txt") == "test_non_lrm_"


def test_detect_prefix_non_lrm_underscore_override(ct, ct_helpers):
    """Non_lrm (underscore variant) also overrides prefix."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto r = Parse(src);"])
    assert _detect_prefix(t, "non_lrm", "/tmp/lrm.txt") == "test_non_lrm_"


def test_detect_prefix_no_match_fallback(ct, ct_helpers, monkeypatch):
    """Falls back to Claude when no obvious pattern matches."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda _p, _s=None, **_kw: {
            "pipeline_stage": "simulator", "rationale": "r",
        },
    )
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_simulator_"


def test_detect_prefix_fallback_stores_rationale(ct, ct_helpers, monkeypatch):
    """Fallback stores prefix_rationale on the test block."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda _p, _s=None, **_kw: {
            "pipeline_stage": "simulator",
            "rationale": "timing checks",
        },
    )
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    _detect_prefix(t, "6.1", "/tmp/lrm.txt")
    assert t.prefix_rationale == "timing checks"


def test_detect_prefix_pattern_match_rationale(ct, ct_helpers):
    """Pattern match stores rationale mentioning matched pattern."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    t = _tb("T", body=["  auto r = Parse(src);"])
    _detect_prefix(t, "6.1", "/tmp/lrm.txt")
    assert "Parse" in t.prefix_rationale


def test_detect_prefix_fallback_calls_claude(ct, ct_helpers, monkeypatch):
    """Fallback invokes _call_claude with prefix prompt."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    calls = []

    def spy(prompt, _schema=None, **_kw):
        calls.append(prompt)
        return {"pipeline_stage": "simulator", "rationale": "r"}

    monkeypatch.setattr(ct, "_call_claude", spy)
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    _detect_prefix(t, "6.1", "/tmp/lrm.txt")
    assert "pipeline stage" in calls[0].lower()


def test_detect_prefix_fallback_invalid_stage_exits(ct, ct_helpers, monkeypatch):
    """Exits when Claude returns an unrecognized pipeline stage."""
    _tb = ct_helpers.make_test_block
    _detect_prefix = getattr(ct, "_detect_prefix")
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda _p, _s=None, **_kw: {
            "pipeline_stage": "bogus", "rationale": "r",
        },
    )
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    with pytest.raises(SystemExit):
        _detect_prefix(t, "6.1", "/tmp/lrm.txt")


# ---- _build_clause_prompt --------------------------------------------------


def test_build_clause_prompt_contains_lrm_path(ct, ct_helpers, tmp_path):
    """Clause prompt includes the LRM file path."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = getattr(ct, "_build_clause_prompt")
    lrm = tmp_path / "LRM.txt"
    t = _tb("X")
    prompt = _build_clause_prompt(t, lrm)
    assert str(lrm) in prompt


def test_build_clause_prompt_contains_test_body(ct, ct_helpers, tmp_path):
    """Clause prompt includes the test's source code."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = getattr(ct, "_build_clause_prompt")
    t = _tb("MyTest")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "TEST(S, MyTest)" in prompt


def test_build_clause_prompt_no_prefix_instructions(ct, ct_helpers, tmp_path):
    """Clause prompt does not mention pipeline prefixes."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = getattr(ct, "_build_clause_prompt")
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "test_parser_" not in prompt


def test_build_clause_prompt_no_arch_path(ct, ct_helpers, tmp_path):
    """Clause prompt does not reference architecture file."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = getattr(ct, "_build_clause_prompt")
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "architecture" not in prompt.lower()


def test_build_clause_prompt_no_file_context(ct, ct_helpers, tmp_path):
    """Clause prompt does not include FILE CONTEXT."""
    _tb = ct_helpers.make_test_block
    _build_clause_prompt = getattr(ct, "_build_clause_prompt")
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "FILE CONTEXT" not in prompt


# ---- _build_topic_prompt ---------------------------------------------------


def test_build_topic_prompt_no_topics(ct, ct_helpers, tmp_path):
    """Topic prompt without existing topics omits hint."""
    _tb = ct_helpers.make_test_block
    _build_topic_prompt = getattr(ct, "_build_topic_prompt")
    t = _tb("X")
    prompt = _build_topic_prompt(t, tmp_path)
    assert "Existing topic files" not in prompt


def test_build_topic_prompt_with_topics(ct, ct_helpers, tmp_path):
    """Topic prompt with existing topics includes hint."""
    _tb = ct_helpers.make_test_block
    _build_topic_prompt = getattr(ct, "_build_topic_prompt")
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    t = _tb("X")
    prompt = _build_topic_prompt(t, tmp_path)
    assert "Existing topic files" in prompt


def test_build_topic_prompt_contains_test_body(ct, ct_helpers, tmp_path):
    """Topic prompt includes the test's source code."""
    _tb = ct_helpers.make_test_block
    _build_topic_prompt = getattr(ct, "_build_topic_prompt")
    t = _tb("MyTest")
    prompt = _build_topic_prompt(t, tmp_path)
    assert "TEST(S, MyTest)" in prompt


# ---- _extract_json ---------------------------------------------------------


def test_extract_json_direct(ct):
    """Parses clean JSON directly."""
    _extract_json = getattr(ct, "_extract_json")
    assert _extract_json('{"a": 1}') == {"a": 1}


def test_extract_json_embedded(ct):
    """Extracts JSON embedded in surrounding text."""
    _extract_json = getattr(ct, "_extract_json")
    text = 'Here is the answer: {"a": 1} done.'
    assert _extract_json(text) == {"a": 1}


def test_extract_json_invalid(ct):
    """Exits when no valid JSON can be extracted."""
    _extract_json = getattr(ct, "_extract_json")
    with pytest.raises(SystemExit):
        _extract_json("no json here")


def test_extract_json_embedded_invalid(ct):
    """Exits when embedded braces contain invalid JSON."""
    _extract_json = getattr(ct, "_extract_json")
    with pytest.raises(SystemExit):
        _extract_json("prefix {not json} suffix")


# ---- _call_claude ----------------------------------------------------------


def test_call_claude_success(ct, monkeypatch):
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


def test_call_claude_raw_text_fallback(ct, monkeypatch):
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


def test_call_claude_structured_output(ct, monkeypatch):
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


def test_call_claude_failure(ct, ct_helpers, monkeypatch):
    """Exits on non-zero return code."""
    _call_claude = getattr(ct, "_call_claude")
    ct_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        _call_claude("prompt")


def _capture_claude_cmd(ct, monkeypatch, schema=None,
                        continue_session=False):
    """Run _call_claude and return the captured subprocess command."""
    _call_claude = getattr(ct, "_call_claude")
    captured_cmd = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = '{"clause": "6.1", "rationale": "r"}'
    mock_result.stderr = ""

    def capture_run(*args, **_kwargs):
        captured_cmd.extend(args[0])
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    _call_claude("prompt", schema=schema,
                 continue_session=continue_session)
    return captured_cmd


def test_call_claude_uses_opus(ct, monkeypatch):
    """CLI command includes --model opus."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    idx = cmd.index("--model")
    assert cmd[idx + 1] == "opus"


def test_call_claude_passes_effort_high(ct, monkeypatch):
    """CLI command includes --effort high."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    idx = cmd.index("--effort")
    assert cmd[idx + 1] == "high"


def test_call_claude_output_format_json(ct, monkeypatch):
    """CLI command includes --output-format json."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    idx = cmd.index("--output-format")
    assert cmd[idx + 1] == "json"


def test_call_claude_uses_dangerously_skip_permissions(ct, monkeypatch):
    """CLI command includes --dangerously-skip-permissions."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--dangerously-skip-permissions" in cmd


def test_call_claude_json_schema(ct, monkeypatch):
    """CLI command includes --json-schema when schema is provided."""
    schema = '{"type": "object"}'
    cmd = _capture_claude_cmd(ct, monkeypatch, schema=schema)
    idx = cmd.index("--json-schema")
    assert cmd[idx + 1] == schema


def test_call_claude_no_json_schema_by_default(ct, monkeypatch):
    """CLI command omits --json-schema when no schema is provided."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--json-schema" not in cmd


def test_call_claude_no_continue_by_default(ct, monkeypatch):
    """CLI command omits --continue by default."""
    cmd = _capture_claude_cmd(ct, monkeypatch)
    assert "--continue" not in cmd


def test_call_claude_with_continue(ct, monkeypatch):
    """CLI command includes --continue when continue_session=True."""
    cmd = _capture_claude_cmd(ct, monkeypatch, continue_session=True)
    assert "--continue" in cmd


def test_call_claude_timeout_retries_then_succeeds(ct, monkeypatch):
    """Retries on timeout and returns result on subsequent success."""
    _call_claude = getattr(ct, "_call_claude")
    monkeypatch.setattr(time, "sleep", lambda _s: None)
    mock_ok = MagicMock()
    mock_ok.returncode = 0
    mock_ok.stdout = '{"clause": "6.1", "rationale": "r"}'
    mock_ok.stderr = ""
    calls = []

    def run_side_effect(*args, **kwargs):
        calls.append(1)
        if len(calls) == 1:
            raise subprocess.TimeoutExpired(args[0], kwargs.get("timeout"))
        return mock_ok

    monkeypatch.setattr(subprocess, "run", run_side_effect)
    assert _call_claude("prompt") == {"clause": "6.1", "rationale": "r"}


def test_call_claude_timeout_exhausted(ct, monkeypatch):
    """Exits after all retry attempts are exhausted by timeouts."""
    _call_claude = getattr(ct, "_call_claude")
    monkeypatch.setattr(time, "sleep", lambda _s: None)

    def run_timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(args[0], kwargs.get("timeout"))

    monkeypatch.setattr(subprocess, "run", run_timeout)
    with pytest.raises(SystemExit):
        _call_claude("prompt")


def test_call_claude_failure_retries_then_succeeds(ct, monkeypatch):
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
    calls = []

    def run_side_effect(*_args, **_kwargs):
        calls.append(1)
        if len(calls) == 1:
            return mock_fail
        return mock_ok

    monkeypatch.setattr(subprocess, "run", run_side_effect)
    assert _call_claude("prompt") == {"clause": "6.1", "rationale": "r"}


def test_call_claude_failure_exhausted(ct, monkeypatch):
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


def test_apply_classification_found(ct, ct_helpers):
    """Applies prefix, clause, and rationale from clause response."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("MyTest", body=["  auto r = Parse(src);"])
    clause_resp = {
        "clause": "6.1", "rationale": "reason",
        "suite_name": "Parsing", "test_name": "MyTest",
    }
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.prefix == "test_parser_" and t.clause == "6.1"


def test_apply_classification_non_lrm_underscore(ct, ct_helpers):
    """Normalizes non_lrm to non-lrm."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non_lrm", "rationale": "r",
                   "suite_name": "S", "test_name": "T"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r",
                  "suite_name": "AigGraph", "test_name": "BasicOp"}
    _apply_classification(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    assert t.clause == "non-lrm:aig"


def _apply_non_lrm_aig(ct, ct_helpers):
    """Apply non-lrm classification with aig topic, return test block."""
    apply_fn = getattr(ct, "_apply_classification")
    t = ct_helpers.make_test_block("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non-lrm", "rationale": "r",
                   "suite_name": "S", "test_name": "T"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r",
                  "suite_name": "AigGraph", "test_name": "BasicOp"}
    apply_fn(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    return t


def test_apply_classification_non_lrm_with_topic(ct, ct_helpers):
    """Appends topic to non-lrm clause."""
    t = _apply_non_lrm_aig(ct, ct_helpers)
    assert t.clause == "non-lrm:aig"


def test_apply_classification_no_rationale(ct, ct_helpers):
    """Missing rationale defaults to empty string."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "6.1", "suite_name": "S", "test_name": "T"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.rationale == ""


def test_apply_classification_non_lrm_empty_topic(ct, ct_helpers):
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


def test_apply_classification_detects_prefix(ct, ct_helpers):
    """Prefix is derived mechanically from test body."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto* d = Elaborate(src);"])
    clause_resp = {"clause": "6.1", "rationale": "r",
                   "suite_name": "Elaboration", "test_name": "T"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.prefix == "test_elaborator_"


def test_apply_classification_non_lrm_prefix_override(ct, ct_helpers):
    """Non-LRM clause overrides prefix to test_non_lrm_."""
    t = _apply_non_lrm_aig(ct, ct_helpers)
    assert t.prefix == "test_non_lrm_"


# ---- classify_test_block ----------------------------------------------------


def test_classify_block_sends_preamble_when_no_continue(
    ct, ct_helpers, monkeypatch, tmp_path,
):
    """classify_test_block sends LRM preamble when continue_session=False."""
    _tb = ct_helpers.make_test_block
    prompts = []

    def capturing_claude(prompt, schema=None, **_kw):
        prompts.append(prompt)
        if schema:
            return {"clause": "6.1", "rationale": "r",
                    "suite_name": "S", "test_name": "T"}
        return "ok"

    monkeypatch.setattr(ct, "_call_claude", capturing_claude)
    t = _tb("T", body=["  auto r = Parse(src);"])
    ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt",
        continue_session=False, clause_hint="6",
    )
    assert "General or Overview" in prompts[0]


def test_classify_block_skips_preamble_when_continue(
    ct, ct_helpers, monkeypatch, tmp_path,
):
    """classify_test_block skips preamble when continue_session=True."""
    _tb = ct_helpers.make_test_block
    prompts = []

    def capturing_claude(prompt, schema=None, **_kw):
        prompts.append(prompt)
        return {"clause": "6.1", "rationale": "r",
                "suite_name": "S", "test_name": "T"}

    monkeypatch.setattr(ct, "_call_claude", capturing_claude)
    t = _tb("T", body=["  auto r = Parse(src);"])
    ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt",
        continue_session=True, clause_hint="6",
    )
    assert "General or Overview" not in prompts[0]


def test_classify_tests_matching(ct, ct_helpers, monkeypatch, tmp_path):
    """classify_test_block applies classification per test."""
    _tb = ct_helpers.make_test_block
    clause_resp = {"clause": "6.1", "rationale": "r",
                   "suite_name": "Parsing", "test_name": "T"}
    monkeypatch.setattr(
        ct, "_call_claude",
        lambda p, schema=None, **_kw: clause_resp,
    )
    t = _tb("T", body=["  auto r = Parse(src);"])
    ct.classify_test_block(
        t, tmp_path, tmp_path / "lrm.txt",
    )
    assert t.prefix == "test_parser_"


def _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path):
    """Classify a non-LRM test and return (call_count, test)."""
    _tb = ct_helpers.make_test_block
    call_count = [0]

    def two_call_claude(_prompt, _schema=None, **_kw):
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


def test_classify_tests_non_lrm_call_count(ct, ct_helpers, monkeypatch, tmp_path):
    """classify_tests makes two Claude calls for non-LRM tests."""
    count, _ = _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path)
    assert count == 2


def test_classify_tests_non_lrm_clause(ct, ct_helpers, monkeypatch, tmp_path):
    """classify_tests sets clause to non-lrm:aig for non-LRM tests."""
    _, t = _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path)
    assert t.clause == "non-lrm:aig"


def test_classify_tests_non_lrm_prefix(ct, ct_helpers, monkeypatch, tmp_path):
    """classify_tests sets prefix to test_non_lrm_ for non-LRM tests."""
    _, t = _do_non_lrm_two_calls(ct, ct_helpers, monkeypatch, tmp_path)
    assert t.prefix == "test_non_lrm_"


# ---- _validate_clause_response helpers -------------------------------------


def _valid_clause(**overrides):
    """Build a minimal valid clause response."""
    base = {"clause": "6.1", "rationale": "r",
            "suite_name": "S", "test_name": "T"}
    base.update(overrides)
    return base


def _valid_topic(**overrides):
    """Build a valid topic response."""
    base = {"non_lrm_topic": "aig", "rationale": "r",
            "suite_name": "S", "test_name": "T"}
    base.update(overrides)
    return base


# ---- _validate_clause_response: required keys ------------------------------


def test_validate_clause_response_missing_clause(ct):
    """Exits when response is missing the clause key."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response({"rationale": "r"}, "T")


# ---- _validate_clause_response: clause format ------------------------------


def test_validate_clause_response_invalid_clause_letters(ct):
    """Exits when clause is arbitrary text."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause="abc"), "T")


def test_validate_clause_response_invalid_clause_empty(ct):
    """Exits when clause is an empty string."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause=""), "T")


def test_validate_clause_response_invalid_clause_trailing_dot(ct):
    """Exits when clause has a trailing dot."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause="6.1."), "T")


def test_validate_clause_response_clause_single_digit(ct):
    """Accepts a single-digit clause."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(
        _valid_clause(clause="6"), "T",
    ) is None


def test_validate_clause_response_clause_deep_numeric(ct):
    """Accepts a deeply nested numeric clause."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(
        _valid_clause(clause="9.2.2.2.2"), "T",
    ) is None


def test_validate_clause_response_clause_annex(ct):
    """Accepts an annex clause like A.6.3."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(
        _valid_clause(clause="A.6.3"), "T",
    ) is None


def test_validate_clause_response_valid(ct):
    """Accepts a valid clause response."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    assert _validate_clause_response(_valid_clause(), "T") is None


# ---- _validate_topic_response ----------------------------------------------


def test_validate_topic_response_missing_topic(ct):
    """Exits when response has no non_lrm_topic key."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    with pytest.raises(SystemExit):
        _validate_topic_response({"rationale": "r"}, "T")


def test_validate_topic_response_null_topic(ct):
    """Exits when non_lrm_topic is None."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    with pytest.raises(SystemExit):
        _validate_topic_response(
            _valid_topic(non_lrm_topic=None), "T",
        )


def test_validate_topic_response_empty_topic(ct):
    """Exits when non_lrm_topic is empty string."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    with pytest.raises(SystemExit):
        _validate_topic_response(_valid_topic(non_lrm_topic=""), "T")


def test_validate_topic_response_valid(ct):
    """Accepts a valid topic response."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    assert _validate_topic_response(_valid_topic(), "T") is None


# ---- _validate_clause_response: error messages -----------------------------


def test_validate_clause_response_invalid_clause_message(ct, capsys):
    """Error message contains the invalid clause value."""
    _validate_clause_response = getattr(ct, "_validate_clause_response")
    try:
        _validate_clause_response(_valid_clause(clause="abc"), "T")
    except SystemExit:
        pass
    assert "abc" in capsys.readouterr().out


def test_validate_topic_response_missing_topic_message(ct, capsys):
    """Error message mentions topic."""
    _validate_topic_response = getattr(ct, "_validate_topic_response")
    try:
        _validate_topic_response({"rationale": "r"}, "T")
    except SystemExit:
        pass
    assert "topic" in capsys.readouterr().out.lower()


# ---- integration: _apply_classification + validation -----------------------


def test_apply_classification_rejects_bad_clause(ct, ct_helpers):
    """_apply_classification exits on an invalid clause."""
    _tb = ct_helpers.make_test_block
    _apply_classification = getattr(ct, "_apply_classification")
    t = _tb("T", body=["  auto r = Parse(src);"])
    with pytest.raises(SystemExit):
        _apply_classification(
            t, _valid_clause(clause="abc"), lrm_path="/tmp/lrm.txt",
        )


def test_classify_tests_propagates_validation_error(ct, ct_helpers, monkeypatch, tmp_path):
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


def test_clause_schema_has_suite_name(ct):
    """CLAUSE_SCHEMA includes a suite_name property."""
    schema = json.loads(getattr(ct, "_CLAUSE_SCHEMA"))
    assert "suite_name" in schema["properties"]


def test_clause_schema_has_test_name(ct):
    """CLAUSE_SCHEMA includes a test_name property."""
    schema = json.loads(getattr(ct, "_CLAUSE_SCHEMA"))
    assert "test_name" in schema["properties"]


def test_clause_prompt_mentions_suite_name(ct):
    """CLAUSE_PROMPT_TEMPLATE instructs Claude to return a suite name."""
    assert "suite_name" in getattr(ct, "_CLAUSE_PROMPT_TEMPLATE")


def test_topic_schema_has_suite_name(ct):
    """TOPIC_SCHEMA includes a suite_name property."""
    schema = json.loads(getattr(ct, "_TOPIC_SCHEMA"))
    assert "suite_name" in schema["properties"]


def test_topic_schema_has_test_name(ct):
    """TOPIC_SCHEMA includes a test_name property."""
    schema = json.loads(getattr(ct, "_TOPIC_SCHEMA"))
    assert "test_name" in schema["properties"]


# ---- _apply_classification: renaming ---------------------------------------


def _apply_with_names(ct, *, macro="TEST"):
    """Apply a clause response with suite_name+test_name, return test block."""
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


def test_apply_classification_renames_suite(ct):
    """Updates test.suite_name to the new suite name."""
    assert _apply_with_names(ct).suite_name == "BinaryOps"


def test_apply_classification_renames_test_name(ct):
    """Updates test.test_name to the new test name."""
    assert _apply_with_names(ct).test_name == "ParseAddition"


def test_apply_classification_renames_test_line(ct):
    """Renames both args in TEST() line."""
    t = _apply_with_names(ct)
    assert t.lines[0] == "TEST(BinaryOps, ParseAddition) {"


def test_apply_classification_renames_test_f(ct):
    """Renames both args in TEST_F() line."""
    t = _apply_with_names(ct, macro="TEST_F")
    assert t.lines[0] == "TEST_F(BinaryOps, ParseAddition) {"


def test_apply_classification_renames_test_p(ct):
    """Renames both args in TEST_P() line."""
    t = _apply_with_names(ct, macro="TEST_P")
    assert t.lines[0] == "TEST_P(BinaryOps, ParseAddition) {"


def test_rename_preserves_original_test_name(ct):
    """Second rename keeps the original_test_name from the first rename."""
    _rename = getattr(ct, "_rename_test_macro")
    t = ct.TestBlock(
        suite_name="S", test_name="First",
        lines=["TEST(S, First) {"], preceding_comments=[],
    )
    _rename(t, "A", "Second")
    _rename(t, "B", "Third")
    assert t.original_test_name == "First"
