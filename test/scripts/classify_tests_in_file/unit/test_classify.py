"""Unit tests for classification functions in classify_tests_in_file."""

import json
import subprocess
from unittest.mock import MagicMock

import pytest

import classify_tests_in_file
from helpers import make_parsed_file as _parsed
from helpers import make_test_block as _tb

_build_prompt = getattr(classify_tests_in_file, "_build_prompt")
_extract_json = getattr(classify_tests_in_file, "_extract_json")
_call_claude = getattr(classify_tests_in_file, "_call_claude")
_apply_classification = getattr(classify_tests_in_file, "_apply_classification")
_validate_response = getattr(
    classify_tests_in_file, "_validate_response", None,
)


# ---- existing_non_lrm_topics ----------------------------------------------


def test_existing_non_lrm_topics_empty(tmp_path):
    """Returns [] when no matching files exist."""
    assert classify_tests_in_file.existing_non_lrm_topics(tmp_path) == []


def test_existing_non_lrm_topics_simple(tmp_path):
    """Returns topic name without letter suffix."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    assert classify_tests_in_file.existing_non_lrm_topics(tmp_path) == ["aig"]


def test_existing_non_lrm_topics_letter_suffix(tmp_path):
    """Strips single letter suffix (e.g., _a) from topic."""
    (tmp_path / "test_non_lrm_arena_a.cpp").write_text("")
    assert classify_tests_in_file.existing_non_lrm_topics(tmp_path) == ["arena"]


def test_existing_non_lrm_topics_short_topic(tmp_path):
    """Short topic (1 char) does not trigger suffix stripping."""
    (tmp_path / "test_non_lrm_x.cpp").write_text("")
    assert classify_tests_in_file.existing_non_lrm_topics(tmp_path) == ["x"]


def test_existing_non_lrm_topics_empty_topic(tmp_path):
    """File whose stem after prefix is empty is skipped."""
    (tmp_path / "test_non_lrm_.cpp").write_text("")
    assert classify_tests_in_file.existing_non_lrm_topics(tmp_path) == []


# ---- _build_prompt ---------------------------------------------------------


def test_build_prompt_no_topics(tmp_path):
    """Prompt without existing non-lrm topics omits hint."""
    t = _tb("X")
    parsed = _parsed()
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "Existing non-lrm topic files" not in prompt


def test_build_prompt_with_topics(tmp_path):
    """Prompt with existing non-lrm topics includes hint."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    t = _tb("X")
    parsed = _parsed()
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "Existing non-lrm topic files" in prompt


def test_build_prompt_no_context(tmp_path):
    """Prompt omits FILE CONTEXT when includes and preamble are empty."""
    t = _tb("X")
    parsed = _parsed()
    parsed.includes = []
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "FILE CONTEXT" not in prompt


def test_build_prompt_contains_lrm_path(tmp_path):
    """Prompt includes the LRM file path."""
    lrm = tmp_path / "LRM.txt"
    t = _tb("X")
    parsed = _parsed()
    prompt = _build_prompt(t, parsed, tmp_path, lrm, tmp_path / "arch.md")
    assert str(lrm) in prompt


def test_build_prompt_contains_arch_path(tmp_path):
    """Prompt includes the architecture file path."""
    arch = tmp_path / "ARCHITECTURE.md"
    t = _tb("X")
    parsed = _parsed()
    prompt = _build_prompt(t, parsed, tmp_path, tmp_path / "lrm.txt", arch)
    assert str(arch) in prompt


def test_build_prompt_contains_test_body(tmp_path):
    """Prompt includes the test's source code."""
    t = _tb("MyTest")
    parsed = _parsed()
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "TEST(S, MyTest)" in prompt


def test_build_prompt_contains_parser_prefix(tmp_path):
    """Prompt lists the parser prefix."""
    t = _tb("X")
    parsed = _parsed()
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "test_parser_" in prompt


def test_build_prompt_contains_non_lrm_prefix(tmp_path):
    """Prompt lists the non-lrm prefix."""
    t = _tb("X")
    parsed = _parsed()
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "test_non_lrm_" in prompt


def test_build_prompt_contains_source_filename(tmp_path):
    """Prompt includes the source filename."""
    t = _tb("X")
    parsed = _parsed()
    parsed.source_filename = "test_non_lrm_misc.cpp"
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "test_non_lrm_misc.cpp" in prompt


def test_build_prompt_contains_includes(tmp_path):
    """Prompt includes #include directives from the parsed file."""
    t = _tb("X")
    parsed = _parsed(includes=[
        '#include <gtest/gtest.h>',
        '#include "parser/parser.h"',
    ])
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert '#include "parser/parser.h"' in prompt


def test_build_prompt_contains_preamble_context(tmp_path):
    """Prompt includes helper definitions from global + section preamble."""
    pre = classify_tests_in_file.PreambleItem(
        lines=["static bool ParseOk(const std::string& src) {", "}"],
    )
    t = _tb("X")
    parsed = _parsed(preamble=[pre])
    prompt = _build_prompt(
        t, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert "ParseOk" in prompt


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
    inner = '{"prefix": "test_parser_"}'
    envelope = json.dumps({"result": inner, "session_id": "x"})
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = envelope
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"prefix": "test_parser_"}


def test_call_claude_raw_text_fallback(monkeypatch):
    """Falls back to _extract_json when stdout is not valid JSON."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = 'Here is the answer: {"prefix": "test_parser_"}'
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"prefix": "test_parser_"}


def test_call_claude_failure(monkeypatch):
    """Exits on non-zero return code."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    with pytest.raises(SystemExit):
        _call_claude("prompt")


def _capture_claude_cmd(monkeypatch):
    """Run _call_claude and return the captured subprocess command."""
    captured_cmd = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = '{"prefix": "test_parser_"}'
    mock_result.stderr = ""

    def capture_run(*args, **_kwargs):
        captured_cmd.extend(args[0])
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    _call_claude("prompt")
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


# ---- _apply_classification -------------------------------------------------


def test_apply_classification_found():
    """Applies prefix, clause, and rationale from response."""
    t = _tb("MyTest")
    resp = {
        "prefix": "test_parser_", "clause": "6.1",
        "rationale": "reason",
    }
    _apply_classification(t, resp)
    assert t.prefix == "test_parser_" and t.clause == "6.1"


def test_apply_classification_non_lrm_underscore():
    """Normalizes non_lrm to non-lrm."""
    t = _tb("T")
    resp = {
        "prefix": "test_non_lrm_", "clause": "non_lrm",
        "non_lrm_topic": "aig",
    }
    _apply_classification(t, resp)
    assert t.clause == "non-lrm:aig"


def test_apply_classification_non_lrm_with_topic():
    """Appends topic to non-lrm clause."""
    t = _tb("T")
    resp = {
        "prefix": "test_non_lrm_", "clause": "non-lrm",
        "non_lrm_topic": "aig",
    }
    _apply_classification(t, resp)
    assert t.clause == "non-lrm:aig"


def test_apply_classification_no_rationale():
    """Missing rationale defaults to empty string."""
    t = _tb("T")
    resp = {"prefix": "test_parser_", "clause": "6.1"}
    _apply_classification(t, resp)
    assert t.rationale == ""


def test_apply_classification_non_lrm_no_topic():
    """non-lrm clause without topic causes SystemExit."""
    t = _tb("T")
    resp = {
        "prefix": "test_non_lrm_", "clause": "non-lrm",
        "non_lrm_topic": None,
    }
    with pytest.raises(SystemExit):
        _apply_classification(t, resp)


# ---- classify_tests --------------------------------------------------------


def test_classify_tests_matching(monkeypatch, tmp_path):
    """classify_tests applies classification per test."""
    response = {
        "prefix": "test_parser_", "clause": "6.1", "rationale": "r",
    }
    monkeypatch.setattr(
        classify_tests_in_file, "_call_claude", lambda p: response,
    )
    t = _tb("T")
    parsed = _parsed()
    classify_tests_in_file.classify_tests(
        [t], parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert t.prefix == "test_parser_"


def test_classify_tests_per_test(monkeypatch, tmp_path):
    """classify_tests calls Claude once per test."""
    call_count = [0]

    def counting_claude(_prompt):
        call_count[0] += 1
        return {
            "prefix": "test_parser_", "clause": "6.1",
            "rationale": "r",
        }

    monkeypatch.setattr(
        classify_tests_in_file, "_call_claude", counting_claude,
    )
    tests = [_tb("A"), _tb("B"), _tb("C")]
    parsed = _parsed()
    classify_tests_in_file.classify_tests(
        tests, parsed, tmp_path, tmp_path / "lrm.txt", tmp_path / "arch.md",
    )
    assert call_count[0] == 3


# ---- _validate_response helpers --------------------------------------------


def _valid_resp(**overrides):
    """Build a minimal valid classification response."""
    base = {"prefix": "test_parser_", "clause": "6.1", "rationale": "r"}
    base.update(overrides)
    return base


def _non_lrm_resp(**overrides):
    """Build a valid non-lrm classification response."""
    base = {
        "prefix": "test_non_lrm_", "clause": "non-lrm",
        "non_lrm_topic": "aig", "rationale": "r",
    }
    base.update(overrides)
    return base


# ---- _validate_response: required keys ------------------------------------


def test_validate_response_missing_prefix():
    """Exits when response is missing the prefix key."""
    with pytest.raises(SystemExit):
        _validate_response({"clause": "6.1"}, "T")


def test_validate_response_missing_clause():
    """Exits when response is missing the clause key."""
    with pytest.raises(SystemExit):
        _validate_response({"prefix": "test_parser_"}, "T")


# ---- _validate_response: prefix -------------------------------------------


def test_validate_response_invalid_prefix():
    """Exits when prefix is not one of the valid seven."""
    with pytest.raises(SystemExit):
        _validate_response(_valid_resp(prefix="test_invalid_"), "T")


def test_validate_response_prefix_no_trailing_underscore():
    """Exits when prefix is missing its trailing underscore."""
    with pytest.raises(SystemExit):
        _validate_response(_valid_resp(prefix="test_parser"), "T")


def test_validate_response_valid_prefix():
    """Accepts a valid prefix without raising."""
    assert _validate_response(_valid_resp(), "T") is None


# ---- _validate_response: clause format ------------------------------------


def test_validate_response_invalid_clause_letters():
    """Exits when clause is arbitrary text."""
    with pytest.raises(SystemExit):
        _validate_response(_valid_resp(clause="abc"), "T")


def test_validate_response_invalid_clause_empty():
    """Exits when clause is an empty string."""
    with pytest.raises(SystemExit):
        _validate_response(_valid_resp(clause=""), "T")


def test_validate_response_invalid_clause_trailing_dot():
    """Exits when clause has a trailing dot."""
    with pytest.raises(SystemExit):
        _validate_response(_valid_resp(clause="6.1."), "T")


def test_validate_response_clause_single_digit():
    """Accepts a single-digit clause."""
    assert _validate_response(_valid_resp(clause="6"), "T") is None


def test_validate_response_clause_deep_numeric():
    """Accepts a deeply nested numeric clause."""
    assert _validate_response(_valid_resp(clause="9.2.2.2.2"), "T") is None


def test_validate_response_clause_annex():
    """Accepts an annex clause like A.6.3."""
    assert _validate_response(_valid_resp(clause="A.6.3"), "T") is None


# ---- _validate_response: non-lrm topic ------------------------------------


def test_validate_response_non_lrm_missing_topic():
    """Exits when non-lrm clause has no non_lrm_topic key."""
    resp = _non_lrm_resp()
    del resp["non_lrm_topic"]
    with pytest.raises(SystemExit):
        _validate_response(resp, "T")


def test_validate_response_non_lrm_null_topic():
    """Exits when non-lrm clause has null topic."""
    with pytest.raises(SystemExit):
        _validate_response(_non_lrm_resp(non_lrm_topic=None), "T")


def test_validate_response_non_lrm_empty_topic():
    """Exits when non-lrm clause has empty string topic."""
    with pytest.raises(SystemExit):
        _validate_response(_non_lrm_resp(non_lrm_topic=""), "T")


def test_validate_response_non_lrm_with_topic():
    """Accepts non-lrm clause with a valid topic."""
    assert _validate_response(_non_lrm_resp(), "T") is None


# ---- _validate_response: error messages ------------------------------------


def test_validate_response_invalid_prefix_message(capsys):
    """Error message contains the invalid prefix value."""
    try:
        _validate_response(_valid_resp(prefix="test_bad_"), "T")
    except SystemExit:
        pass
    assert "test_bad_" in capsys.readouterr().out


def test_validate_response_missing_topic_message(capsys):
    """Error message mentions non_lrm_topic."""
    try:
        _validate_response(_non_lrm_resp(non_lrm_topic=None), "T")
    except SystemExit:
        pass
    assert "non_lrm_topic" in capsys.readouterr().out


# ---- _validate_response: integration with _apply_classification ------------


def test_apply_classification_rejects_bad_prefix():
    """_apply_classification exits on an invalid prefix."""
    t = _tb("T")
    with pytest.raises(SystemExit):
        _apply_classification(t, _valid_resp(prefix="test_bad_"))


def test_classify_tests_propagates_validation_error(monkeypatch, tmp_path):
    """classify_tests exits when Claude returns an invalid prefix."""
    monkeypatch.setattr(
        classify_tests_in_file, "_call_claude",
        lambda _p: _valid_resp(prefix="test_bad_"),
    )
    parsed = _parsed()
    with pytest.raises(SystemExit):
        classify_tests_in_file.classify_tests(
            [_tb("T")], parsed, tmp_path,
            tmp_path / "lrm.txt", tmp_path / "arch.md",
        )
