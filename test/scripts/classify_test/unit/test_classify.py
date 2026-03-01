"""Unit tests for classification functions in classify_test."""

import json
import subprocess
from unittest.mock import MagicMock

import pytest

import classify_test
from helpers import make_parsed_file as _parsed
from helpers import make_test_block as _tb
from helpers import stub_subprocess_failure

_detect_prefix = getattr(classify_test, "_detect_prefix")
_build_clause_prompt = getattr(classify_test, "_build_clause_prompt")
_build_topic_prompt = getattr(classify_test, "_build_topic_prompt")
_extract_json = getattr(classify_test, "_extract_json")
_call_claude = getattr(classify_test, "_call_claude")
_apply_classification = getattr(classify_test, "_apply_classification")
_validate_clause_response = getattr(
    classify_test, "_validate_clause_response",
)
_validate_topic_response = getattr(
    classify_test, "_validate_topic_response",
)


# ---- existing_non_lrm_topics ----------------------------------------------


def test_existing_non_lrm_topics_empty(tmp_path):
    """Returns [] when no matching files exist."""
    assert classify_test.existing_non_lrm_topics(tmp_path) == []


def test_existing_non_lrm_topics_simple(tmp_path):
    """Returns topic name without letter suffix."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    assert classify_test.existing_non_lrm_topics(tmp_path) == ["aig"]


def test_existing_non_lrm_topics_letter_suffix(tmp_path):
    """Strips single letter suffix (e.g., _a) from topic."""
    (tmp_path / "test_non_lrm_arena_a.cpp").write_text("")
    assert classify_test.existing_non_lrm_topics(tmp_path) == ["arena"]


def test_existing_non_lrm_topics_short_topic(tmp_path):
    """Short topic (1 char) does not trigger suffix stripping."""
    (tmp_path / "test_non_lrm_x.cpp").write_text("")
    assert classify_test.existing_non_lrm_topics(tmp_path) == ["x"]


def test_existing_non_lrm_topics_empty_topic(tmp_path):
    """File whose stem after prefix is empty is skipped."""
    (tmp_path / "test_non_lrm_.cpp").write_text("")
    assert classify_test.existing_non_lrm_topics(tmp_path) == []


# ---- _detect_prefix --------------------------------------------------------


def test_detect_prefix_parser():
    """Detects parser prefix from Parse( call."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_parser_"


def test_detect_prefix_parser_src():
    """Detects parser prefix from ParseSrc( variant."""
    t = _tb("T", body=["  auto r = ParseSrc(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_parser_"


def test_detect_prefix_elaborator():
    """Detects elaborator prefix from Elaborate( call."""
    t = _tb("T", body=["  auto* d = Elaborate(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_elaborator_"


def test_detect_prefix_elaborator_src():
    """Detects elaborator prefix from ElaborateSrc( variant."""
    t = _tb("T", body=["  auto* d = ElaborateSrc(src, f);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_elaborator_"


def test_detect_prefix_lexer_lex():
    """Detects lexer prefix from Lex( call."""
    t = _tb("T", body=["  auto tok = Lex(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_lexer_"


def test_detect_prefix_lexer_one():
    """Detects lexer prefix from LexOne( variant."""
    t = _tb("T", body=["  auto tok = LexOne(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_lexer_"


def test_detect_prefix_simulator():
    """Detects simulator prefix from Scheduler( call."""
    t = _tb("T", body=["  Scheduler sched;"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_simulator_"


def test_detect_prefix_simulator_sim_context():
    """Detects simulator prefix from SimContext call."""
    t = _tb("T", body=["  SimContext ctx;"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_simulator_"


def test_detect_prefix_synthesizer():
    """Detects synthesizer prefix from SynthLower( call."""
    t = _tb("T", body=["  auto g = SynthLower(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_synthesizer_"


def test_detect_prefix_synthesizer_aig():
    """Detects synthesizer prefix from AigGraph."""
    t = _tb("T", body=["  AigGraph g;"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_synthesizer_"


def test_detect_prefix_preprocessor():
    """Detects preprocessor prefix from Preprocessor( call."""
    t = _tb("T", body=["  Preprocessor pp(src);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_preprocessor_"


def test_detect_prefix_non_lrm_override():
    """Non-LRM clause overrides detected prefix to test_non_lrm_."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    assert _detect_prefix(t, "non-lrm", "/tmp/lrm.txt") == "test_non_lrm_"


def test_detect_prefix_non_lrm_underscore_override():
    """Non_lrm (underscore variant) also overrides prefix."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    assert _detect_prefix(t, "non_lrm", "/tmp/lrm.txt") == "test_non_lrm_"


def test_detect_prefix_no_match_fallback(monkeypatch):
    """Falls back to Claude when no obvious pattern matches."""
    monkeypatch.setattr(
        classify_test, "_call_claude",
        lambda _p, _s=None: {
            "pipeline_stage": "simulator", "rationale": "r",
        },
    )
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    assert _detect_prefix(t, "6.1", "/tmp/lrm.txt") == "test_simulator_"


def test_detect_prefix_fallback_calls_claude(monkeypatch):
    """Fallback invokes _call_claude with prefix prompt."""
    calls = []

    def spy(prompt, schema=None):
        calls.append(prompt)
        return {"pipeline_stage": "simulator", "rationale": "r"}

    monkeypatch.setattr(classify_test, "_call_claude", spy)
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    _detect_prefix(t, "6.1", "/tmp/lrm.txt")
    assert "pipeline stage" in calls[0].lower()


def test_detect_prefix_fallback_invalid_stage_exits(monkeypatch):
    """Exits when Claude returns an unrecognized pipeline stage."""
    monkeypatch.setattr(
        classify_test, "_call_claude",
        lambda _p, _s=None: {
            "pipeline_stage": "bogus", "rationale": "r",
        },
    )
    t = _tb("T", body=["  EvalExpr(ctx, e);"])
    with pytest.raises(SystemExit):
        _detect_prefix(t, "6.1", "/tmp/lrm.txt")


# ---- _build_clause_prompt --------------------------------------------------


def test_build_clause_prompt_contains_lrm_path(tmp_path):
    """Clause prompt includes the LRM file path."""
    lrm = tmp_path / "LRM.txt"
    t = _tb("X")
    prompt = _build_clause_prompt(t, lrm)
    assert str(lrm) in prompt


def test_build_clause_prompt_contains_test_body(tmp_path):
    """Clause prompt includes the test's source code."""
    t = _tb("MyTest")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "TEST(S, MyTest)" in prompt


def test_build_clause_prompt_no_prefix_instructions(tmp_path):
    """Clause prompt does not mention pipeline prefixes."""
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "test_parser_" not in prompt


def test_build_clause_prompt_no_arch_path(tmp_path):
    """Clause prompt does not reference architecture file."""
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "architecture" not in prompt.lower()


def test_build_clause_prompt_no_file_context(tmp_path):
    """Clause prompt does not include FILE CONTEXT."""
    t = _tb("X")
    prompt = _build_clause_prompt(t, tmp_path / "lrm.txt")
    assert "FILE CONTEXT" not in prompt


# ---- _build_topic_prompt ---------------------------------------------------


def test_build_topic_prompt_no_topics(tmp_path):
    """Topic prompt without existing topics omits hint."""
    t = _tb("X")
    prompt = _build_topic_prompt(t, tmp_path)
    assert "Existing topic files" not in prompt


def test_build_topic_prompt_with_topics(tmp_path):
    """Topic prompt with existing topics includes hint."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    t = _tb("X")
    prompt = _build_topic_prompt(t, tmp_path)
    assert "Existing topic files" in prompt


def test_build_topic_prompt_contains_test_body(tmp_path):
    """Topic prompt includes the test's source code."""
    t = _tb("MyTest")
    prompt = _build_topic_prompt(t, tmp_path)
    assert "TEST(S, MyTest)" in prompt


# ---- _extract_json ---------------------------------------------------------


def test_extract_json_direct():
    """Parses clean JSON directly."""
    assert _extract_json('{"a": 1}') == {"a": 1}


def test_extract_json_embedded():
    """Extracts JSON embedded in surrounding text."""
    text = 'Here is the answer: {"a": 1} done.'
    assert _extract_json(text) == {"a": 1}


def test_extract_json_invalid():
    """Exits when no valid JSON can be extracted."""
    with pytest.raises(SystemExit):
        _extract_json("no json here")


def test_extract_json_embedded_invalid():
    """Exits when embedded braces contain invalid JSON."""
    with pytest.raises(SystemExit):
        _extract_json("prefix {not json} suffix")


# ---- _call_claude ----------------------------------------------------------


def test_call_claude_success(monkeypatch):
    """Returns parsed JSON from --output-format json envelope."""
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


def test_call_claude_raw_text_fallback(monkeypatch):
    """Falls back to _extract_json when stdout is not valid JSON."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = 'Here is the answer: {"clause": "6.1"}'
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"clause": "6.1"}


def test_call_claude_structured_output(monkeypatch):
    """Returns structured_output directly when present in envelope."""
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


def test_call_claude_failure(monkeypatch):
    """Exits on non-zero return code."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        _call_claude("prompt")


def _capture_claude_cmd(monkeypatch, schema=None):
    """Run _call_claude and return the captured subprocess command."""
    captured_cmd = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = '{"clause": "6.1", "rationale": "r"}'
    mock_result.stderr = ""

    def capture_run(*args, **_kwargs):
        captured_cmd.extend(args[0])
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    _call_claude("prompt", schema=schema)
    return captured_cmd


def test_call_claude_output_format_json(monkeypatch):
    """CLI command includes --output-format json."""
    cmd = _capture_claude_cmd(monkeypatch)
    idx = cmd.index("--output-format")
    assert cmd[idx + 1] == "json"


def test_call_claude_allows_read(monkeypatch):
    """CLI command includes --allowedTools Read."""
    cmd = _capture_claude_cmd(monkeypatch)
    assert "--allowedTools" in cmd and "Read" in cmd


def test_call_claude_json_schema(monkeypatch):
    """CLI command includes --json-schema when schema is provided."""
    schema = '{"type": "object"}'
    cmd = _capture_claude_cmd(monkeypatch, schema=schema)
    idx = cmd.index("--json-schema")
    assert cmd[idx + 1] == schema


def test_call_claude_no_json_schema_by_default(monkeypatch):
    """CLI command omits --json-schema when no schema is provided."""
    cmd = _capture_claude_cmd(monkeypatch)
    assert "--json-schema" not in cmd


# ---- _apply_classification -------------------------------------------------


def test_apply_classification_found():
    """Applies prefix, clause, and rationale from clause response."""
    t = _tb("MyTest", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "6.1", "rationale": "reason"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.prefix == "test_parser_" and t.clause == "6.1"


def test_apply_classification_non_lrm_underscore():
    """Normalizes non_lrm to non-lrm."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non_lrm", "rationale": "r"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r"}
    _apply_classification(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    assert t.clause == "non-lrm:aig"


def test_apply_classification_non_lrm_with_topic():
    """Appends topic to non-lrm clause."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non-lrm", "rationale": "r"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r"}
    _apply_classification(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    assert t.clause == "non-lrm:aig"


def test_apply_classification_no_rationale():
    """Missing rationale defaults to empty string."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "6.1"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.rationale == ""


def test_apply_classification_non_lrm_empty_topic():
    """non-lrm clause with empty topic causes SystemExit."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non-lrm", "rationale": "r"}
    topic_resp = {"non_lrm_topic": "", "rationale": "r"}
    with pytest.raises(SystemExit):
        _apply_classification(
            t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt",
        )


def test_apply_classification_detects_prefix():
    """Prefix is derived mechanically from test body."""
    t = _tb("T", body=["  auto* d = Elaborate(src);"])
    clause_resp = {"clause": "6.1", "rationale": "r"}
    _apply_classification(t, clause_resp, lrm_path="/tmp/lrm.txt")
    assert t.prefix == "test_elaborator_"


def test_apply_classification_non_lrm_prefix_override():
    """Non-LRM clause overrides prefix to test_non_lrm_."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    clause_resp = {"clause": "non-lrm", "rationale": "r"}
    topic_resp = {"non_lrm_topic": "aig", "rationale": "r"}
    _apply_classification(t, clause_resp, topic_resp, lrm_path="/tmp/lrm.txt")
    assert t.prefix == "test_non_lrm_"


# ---- classify_tests --------------------------------------------------------


def test_classify_tests_matching(monkeypatch, tmp_path):
    """classify_tests applies classification per test."""
    clause_resp = {"clause": "6.1", "rationale": "r"}
    monkeypatch.setattr(
        classify_test, "_call_claude",
        lambda p, schema=None: clause_resp,
    )
    t = _tb("T", body=["  auto r = Parse(src);"])
    classify_test.classify_tests(
        [t], tmp_path, tmp_path / "lrm.txt",
    )
    assert t.prefix == "test_parser_"


def test_classify_tests_per_test(monkeypatch, tmp_path):
    """classify_tests calls Claude once per (non-lrm) test."""
    call_count = [0]

    def counting_claude(_prompt, _schema=None):
        call_count[0] += 1
        return {"clause": "6.1", "rationale": "r"}

    monkeypatch.setattr(
        classify_test, "_call_claude", counting_claude,
    )
    tests = [
        _tb("A", body=["  auto r = Parse(src);"]),
        _tb("B", body=["  auto r = Parse(src);"]),
        _tb("C", body=["  auto r = Parse(src);"]),
    ]
    classify_test.classify_tests(
        tests, tmp_path, tmp_path / "lrm.txt",
    )
    assert call_count[0] == 3


def _do_non_lrm_two_calls(monkeypatch, tmp_path):
    """Classify a non-LRM test and return (call_count, test)."""
    call_count = [0]

    def two_call_claude(_prompt, _schema=None):
        call_count[0] += 1
        if call_count[0] == 1:
            return {"clause": "non-lrm", "rationale": "r"}
        return {"non_lrm_topic": "aig", "rationale": "r"}

    monkeypatch.setattr(
        classify_test, "_call_claude", two_call_claude,
    )
    t = _tb("T", body=["  auto r = Parse(src);"])
    classify_test.classify_tests(
        [t], tmp_path, tmp_path / "lrm.txt",
    )
    return call_count[0], t


def test_classify_tests_non_lrm_call_count(monkeypatch, tmp_path):
    """classify_tests makes two Claude calls for non-LRM tests."""
    count, _ = _do_non_lrm_two_calls(monkeypatch, tmp_path)
    assert count == 2


def test_classify_tests_non_lrm_clause(monkeypatch, tmp_path):
    """classify_tests sets clause to non-lrm:aig for non-LRM tests."""
    _, t = _do_non_lrm_two_calls(monkeypatch, tmp_path)
    assert t.clause == "non-lrm:aig"


def test_classify_tests_non_lrm_prefix(monkeypatch, tmp_path):
    """classify_tests sets prefix to test_non_lrm_ for non-LRM tests."""
    _, t = _do_non_lrm_two_calls(monkeypatch, tmp_path)
    assert t.prefix == "test_non_lrm_"


# ---- _validate_clause_response helpers -------------------------------------


def _valid_clause(**overrides):
    """Build a minimal valid clause response."""
    base = {"clause": "6.1", "rationale": "r"}
    base.update(overrides)
    return base


def _valid_topic(**overrides):
    """Build a valid topic response."""
    base = {"non_lrm_topic": "aig", "rationale": "r"}
    base.update(overrides)
    return base


# ---- _validate_clause_response: required keys ------------------------------


def test_validate_clause_response_missing_clause():
    """Exits when response is missing the clause key."""
    with pytest.raises(SystemExit):
        _validate_clause_response({"rationale": "r"}, "T")


# ---- _validate_clause_response: clause format ------------------------------


def test_validate_clause_response_invalid_clause_letters():
    """Exits when clause is arbitrary text."""
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause="abc"), "T")


def test_validate_clause_response_invalid_clause_empty():
    """Exits when clause is an empty string."""
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause=""), "T")


def test_validate_clause_response_invalid_clause_trailing_dot():
    """Exits when clause has a trailing dot."""
    with pytest.raises(SystemExit):
        _validate_clause_response(_valid_clause(clause="6.1."), "T")


def test_validate_clause_response_clause_single_digit():
    """Accepts a single-digit clause."""
    assert _validate_clause_response(
        _valid_clause(clause="6"), "T",
    ) is None


def test_validate_clause_response_clause_deep_numeric():
    """Accepts a deeply nested numeric clause."""
    assert _validate_clause_response(
        _valid_clause(clause="9.2.2.2.2"), "T",
    ) is None


def test_validate_clause_response_clause_annex():
    """Accepts an annex clause like A.6.3."""
    assert _validate_clause_response(
        _valid_clause(clause="A.6.3"), "T",
    ) is None


def test_validate_clause_response_valid():
    """Accepts a valid clause response."""
    assert _validate_clause_response(_valid_clause(), "T") is None


# ---- _validate_topic_response ----------------------------------------------


def test_validate_topic_response_missing_topic():
    """Exits when response has no non_lrm_topic key."""
    with pytest.raises(SystemExit):
        _validate_topic_response({"rationale": "r"}, "T")


def test_validate_topic_response_null_topic():
    """Exits when non_lrm_topic is None."""
    with pytest.raises(SystemExit):
        _validate_topic_response(
            _valid_topic(non_lrm_topic=None), "T",
        )


def test_validate_topic_response_empty_topic():
    """Exits when non_lrm_topic is empty string."""
    with pytest.raises(SystemExit):
        _validate_topic_response(_valid_topic(non_lrm_topic=""), "T")


def test_validate_topic_response_valid():
    """Accepts a valid topic response."""
    assert _validate_topic_response(_valid_topic(), "T") is None


# ---- _validate_clause_response: error messages -----------------------------


def test_validate_clause_response_invalid_clause_message(capsys):
    """Error message contains the invalid clause value."""
    try:
        _validate_clause_response(_valid_clause(clause="abc"), "T")
    except SystemExit:
        pass
    assert "abc" in capsys.readouterr().out


def test_validate_topic_response_missing_topic_message(capsys):
    """Error message mentions topic."""
    try:
        _validate_topic_response({"rationale": "r"}, "T")
    except SystemExit:
        pass
    assert "topic" in capsys.readouterr().out.lower()


# ---- integration: _apply_classification + validation -----------------------


def test_apply_classification_rejects_bad_clause():
    """_apply_classification exits on an invalid clause."""
    t = _tb("T", body=["  auto r = Parse(src);"])
    with pytest.raises(SystemExit):
        _apply_classification(
            t, _valid_clause(clause="abc"), lrm_path="/tmp/lrm.txt",
        )


def test_classify_tests_propagates_validation_error(monkeypatch, tmp_path):
    """classify_tests exits when Claude returns an invalid clause."""
    monkeypatch.setattr(
        classify_test, "_call_claude",
        lambda _p, schema=None: _valid_clause(clause="abc"),
    )
    with pytest.raises(SystemExit):
        classify_test.classify_tests(
            [_tb("T", body=["  auto r = Parse(src);"])],
            tmp_path, tmp_path / "lrm.txt",
        )
