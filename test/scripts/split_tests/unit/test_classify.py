"""Unit tests for classification functions in split_tests."""

import subprocess
from unittest.mock import MagicMock

import pytest

import split_tests
from helpers import make_test_block as _tb
from helpers import monkeypatch_paths

_build_test_blocks_text = getattr(split_tests, "_build_test_blocks_text")
_build_prompt = getattr(split_tests, "_build_prompt")
_extract_json = getattr(split_tests, "_extract_json")
_call_claude = getattr(split_tests, "_call_claude")
_build_result_map = getattr(split_tests, "_build_result_map")
_apply_classifications = getattr(split_tests, "_apply_classifications")


# ---- load_lrm_toc ---------------------------------------------------------


def test_load_lrm_toc_missing(monkeypatch, tmp_path):
    """Returns placeholder when LRM file is missing."""
    monkeypatch.setattr(split_tests, "LRM_PATH", tmp_path / "no.txt")
    assert split_tests.load_lrm_toc() == "(LRM not found)"


def test_load_lrm_toc_exists(monkeypatch, tmp_path):
    """Returns first 2500 lines of the LRM file."""
    lrm = tmp_path / "LRM.txt"
    lrm.write_text("line1\nline2\n", encoding="utf-8")
    monkeypatch.setattr(split_tests, "LRM_PATH", lrm)
    assert "line1" in split_tests.load_lrm_toc()


# ---- load_architecture -----------------------------------------------------


def test_load_architecture_missing(monkeypatch, tmp_path):
    """Returns placeholder when ARCHITECTURE.md is missing."""
    monkeypatch.setattr(
        split_tests, "ARCH_PATH", tmp_path / "none.md",
    )
    assert split_tests.load_architecture() == "(ARCHITECTURE.md not found)"


def test_load_architecture_exists(monkeypatch, tmp_path):
    """Returns full text of ARCHITECTURE.md."""
    arch = tmp_path / "ARCHITECTURE.md"
    arch.write_text("# Arch", encoding="utf-8")
    monkeypatch.setattr(split_tests, "ARCH_PATH", arch)
    assert split_tests.load_architecture() == "# Arch"


# ---- existing_non_lrm_topics ----------------------------------------------


def test_existing_non_lrm_topics_empty(tmp_path):
    """Returns [] when no matching files exist."""
    assert split_tests.existing_non_lrm_topics(tmp_path) == []


def test_existing_non_lrm_topics_simple(tmp_path):
    """Returns topic name without letter suffix."""
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    assert split_tests.existing_non_lrm_topics(tmp_path) == ["aig"]


def test_existing_non_lrm_topics_letter_suffix(tmp_path):
    """Strips single letter suffix (e.g., _a) from topic."""
    (tmp_path / "test_non_lrm_arena_a.cpp").write_text("")
    assert split_tests.existing_non_lrm_topics(tmp_path) == ["arena"]


def test_existing_non_lrm_topics_short_topic(tmp_path):
    """Short topic (1 char) does not trigger suffix stripping."""
    (tmp_path / "test_non_lrm_x.cpp").write_text("")
    assert split_tests.existing_non_lrm_topics(tmp_path) == ["x"]


def test_existing_non_lrm_topics_empty_topic(tmp_path):
    """File whose stem after prefix is empty is skipped."""
    (tmp_path / "test_non_lrm_.cpp").write_text("")
    assert split_tests.existing_non_lrm_topics(tmp_path) == []


# ---- _build_test_blocks_text ----------------------------------------------


def test_build_test_blocks_text():
    """Builds text representation of test blocks."""
    t = _tb("MyTest", comments=["// doc"])
    result = _build_test_blocks_text([t])
    assert "--- TEST(S, MyTest) ---" in result


# ---- _build_prompt ---------------------------------------------------------


def test_build_prompt_no_topics(monkeypatch, tmp_path):
    """Prompt without existing non-lrm topics omits hint."""
    monkeypatch_paths(monkeypatch, tmp_path)
    t = _tb("X")
    prompt = _build_prompt([t], tmp_path)
    assert "Existing non-lrm topic files" not in prompt


def test_build_prompt_with_topics(monkeypatch, tmp_path):
    """Prompt with existing non-lrm topics includes hint."""
    monkeypatch_paths(monkeypatch, tmp_path)
    (tmp_path / "test_non_lrm_aig.cpp").write_text("")
    t = _tb("X")
    prompt = _build_prompt([t], tmp_path)
    assert "Existing non-lrm topic files" in prompt


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
    mock_result.stdout = '{"tests": []}'
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert _call_claude("prompt") == {"tests": []}


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


def test_call_claude_stderr_printed(monkeypatch, capsys):
    """Prints stderr when present but rc=0."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = '{"tests": []}'
    mock_result.stderr = "warning text"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    _call_claude("prompt")
    assert "warning text" in capsys.readouterr().out


# ---- _build_result_map -----------------------------------------------------


def test_build_result_map_simple():
    """Maps test_name directly."""
    resp = {"tests": [
        {"test_name": "MyTest", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "MyTest" in rm


def test_build_result_map_wrapped_name():
    """Strips TEST(...) wrapper from test_name."""
    resp = {"tests": [
        {"test_name": "TEST(Suite, MyTest)", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "Suite, MyTest" in rm


def test_build_result_map_underscore_separator():
    """Adds entries for the part after common separators."""
    resp = {"tests": [
        {"test_name": "Suite_MyTest", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "MyTest" in rm


def test_build_result_map_dot_separator():
    """Adds entry for part after '.' separator."""
    resp = {"tests": [
        {"test_name": "Suite.MyTest", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "MyTest" in rm


def test_build_result_map_slash_separator():
    """Adds entry for part after '/' separator."""
    resp = {"tests": [
        {"test_name": "Suite/MyTest", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "MyTest" in rm


def test_build_result_map_comma_separator():
    """Adds entry for part after ', ' separator."""
    resp = {"tests": [
        {"test_name": "Suite, MyTest", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "MyTest" in rm


def test_build_result_map_double_colon_separator():
    """Adds entry for part after '::' separator."""
    resp = {"tests": [
        {"test_name": "Suite::MyTest", "prefix": "test_parser_",
         "clause": "6.1"},
    ]}
    rm = _build_result_map(resp)
    assert "MyTest" in rm


def test_build_result_map_empty():
    """Empty response returns empty map."""
    assert not _build_result_map({})


# ---- _apply_classifications ------------------------------------------------


def test_apply_classifications_found():
    """Applies prefix, clause, and rationale from result_map."""
    t = _tb("MyTest")
    rm = {"MyTest": {
        "prefix": "test_parser_", "clause": "6.1",
        "rationale": "reason",
    }}
    _apply_classifications([t], rm)
    assert t.prefix == "test_parser_" and t.clause == "6.1"


def test_apply_classifications_not_found():
    """Defaults to non-lrm when test is not in result_map."""
    t = _tb("Missing")
    _apply_classifications([t], {})
    assert t.prefix == "test_non_lrm"


def test_apply_classifications_non_lrm_underscore():
    """Normalizes non_lrm to non-lrm."""
    t = _tb("T")
    rm = {"T": {
        "prefix": "test_non_lrm_", "clause": "non_lrm",
    }}
    _apply_classifications([t], rm)
    assert t.clause == "non-lrm"


def test_apply_classifications_non_lrm_with_topic():
    """Appends topic to non-lrm clause."""
    t = _tb("T")
    rm = {"T": {
        "prefix": "test_non_lrm_", "clause": "non-lrm",
        "non_lrm_topic": "aig",
    }}
    _apply_classifications([t], rm)
    assert t.clause == "non-lrm:aig"


def test_apply_classifications_no_rationale():
    """Missing rationale defaults to empty string."""
    t = _tb("T")
    rm = {"T": {"prefix": "test_parser_", "clause": "6.1"}}
    _apply_classifications([t], rm)
    assert t.rationale == ""


def test_apply_classifications_non_lrm_no_topic():
    """non-lrm clause without topic stays as non-lrm."""
    t = _tb("T")
    rm = {"T": {
        "prefix": "test_non_lrm_", "clause": "non-lrm",
        "non_lrm_topic": None,
    }}
    _apply_classifications([t], rm)
    assert t.clause == "non-lrm"


# ---- classify_tests --------------------------------------------------------


def test_classify_tests_matching(monkeypatch, tmp_path):
    """classify_tests applies classifications when names match."""
    monkeypatch_paths(monkeypatch, tmp_path)
    response = {"tests": [
        {"test_name": "T", "prefix": "test_parser_",
         "clause": "6.1", "rationale": "r"},
    ]}
    monkeypatch.setattr(
        split_tests, "_call_claude", lambda p: response,
    )
    t = _tb("T")
    split_tests.classify_tests([t], tmp_path)
    assert t.prefix == "test_parser_"


def test_classify_tests_mismatch(monkeypatch, tmp_path, capsys):
    """classify_tests prints warning on name mismatch."""
    monkeypatch_paths(monkeypatch, tmp_path)
    response = {"tests": [
        {"test_name": "Wrong", "prefix": "test_parser_",
         "clause": "6.1", "rationale": "r"},
    ]}
    monkeypatch.setattr(
        split_tests, "_call_claude", lambda p: response,
    )
    t = _tb("T")
    split_tests.classify_tests([t], tmp_path)
    assert "WARNING" in capsys.readouterr().out


def test_classify_tests_no_missing(monkeypatch, tmp_path, capsys):
    """When names differ but result_map has all keys, no mismatch print."""
    monkeypatch_paths(monkeypatch, tmp_path)
    response = {"tests": [
        {"test_name": "Suite_T", "prefix": "test_parser_",
         "clause": "6.1", "rationale": "r"},
    ]}
    monkeypatch.setattr(
        split_tests, "_call_claude", lambda p: response,
    )
    t = _tb("T")
    split_tests.classify_tests([t], tmp_path)
    assert "Name mismatch" not in capsys.readouterr().out
