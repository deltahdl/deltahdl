"""Unit tests for classification functions in classify_tests_in_file."""

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
    parsed = _parsed(source_filename="test_non_lrm_misc.cpp")
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
    """Returns parsed JSON on success."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = '{"prefix": "test_parser_"}'
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
    resp = {"prefix": "test_non_lrm_", "clause": "non_lrm"}
    _apply_classification(t, resp)
    assert t.clause == "non-lrm"


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
    """non-lrm clause without topic stays as non-lrm."""
    t = _tb("T")
    resp = {
        "prefix": "test_non_lrm_", "clause": "non-lrm",
        "non_lrm_topic": None,
    }
    _apply_classification(t, resp)
    assert t.clause == "non-lrm"


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
