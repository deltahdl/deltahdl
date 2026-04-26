"""Unit tests for compute_subclause_dependencies (dependency oracle)."""

import json
import runpy
from unittest.mock import patch

import pytest


# ---- helpers ----------------------------------------------------------------


def _make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


_BASE_ARGS = ["--subclause", "33.4.1.5"]


def _args_with_lrm(tmp_path, *extra):
    """Return CLI args with --lrm pointing at a temp file."""
    return ["--lrm", str(_make_lrm(tmp_path)), *_BASE_ARGS, *extra]


# ---- main argument plumbing ------------------------------------------------


def test_main_requires_subclause(csd, tmp_path):
    """main() exits when --subclause is missing."""
    with pytest.raises(SystemExit):
        csd.main(["--lrm", str(_make_lrm(tmp_path))])


def test_main_requires_lrm(csd):
    """main() exits when --lrm is missing."""
    with pytest.raises(SystemExit):
        csd.main(["--subclause", "4.1"])


def test_main_rejects_bad_clause(csd, tmp_path):
    """main() exits when --subclause is not a valid clause string."""
    with pytest.raises(SystemExit):
        csd.main([
            "--lrm", str(_make_lrm(tmp_path)), "--subclause", "bad",
        ])


# ---- build_prompt ----------------------------------------------------------


def test_build_prompt_mentions_subclause(csd):
    """Prompt mentions the target subclause."""
    assert "§33.4.1.5" in csd.build_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_prompt_mentions_read_only(csd):
    """Prompt explicitly states the oracle is read-only."""
    assert "READ-ONLY" in csd.build_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_prompt_mentions_lrm(csd):
    """Prompt embeds the LRM path."""
    assert "~/LRM.pdf" in csd.build_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_prompt_describes_required_relation(csd):
    """Prompt explains the dependency relation as REQUIRED-before."""
    assert "REQUIRED" in csd.build_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_prompt_describes_parent_rollup(csd):
    """Prompt explains the parent-rolls-up-over-children rule."""
    assert "child" in csd.build_prompt("33.4", "~/LRM.pdf")


def test_build_prompt_requests_json_array(csd):
    """Prompt instructs the oracle to output a single JSON array."""
    assert "JSON array" in csd.build_prompt("33.4.1.5", "~/LRM.pdf")


def test_build_prompt_says_empty_if_none(csd):
    """Prompt instructs an empty array when no dependencies exist."""
    assert "[]" in csd.build_prompt("33.4.1.5", "~/LRM.pdf")


# ---- parse_dependencies -----------------------------------------------------


def test_parse_dependencies_empty(csd):
    """An empty array parses to an empty list."""
    assert csd.parse_dependencies("[]") == []


def test_parse_dependencies_single_entry(csd):
    """A single subclause string parses through verbatim."""
    assert csd.parse_dependencies('["33.6.1"]') == ["33.6.1"]


def test_parse_dependencies_preserves_order(csd):
    """Dependencies are returned in the order the oracle listed them."""
    text = '["33.6.1", "33.4.1.5", "33.4.1.6"]'
    assert csd.parse_dependencies(text) == [
        "33.6.1", "33.4.1.5", "33.4.1.6",
    ]


def test_parse_dependencies_handles_fenced_array(csd):
    """A fenced JSON array oracle response parses."""
    text = '```json\n["33.6.1"]\n```'
    assert csd.parse_dependencies(text) == ["33.6.1"]


def test_parse_dependencies_accepts_annex(csd):
    """An annex-letter dependency entry is accepted."""
    assert csd.parse_dependencies('["A.7"]') == ["A.7"]


def test_parse_dependencies_rejects_object(csd):
    """A JSON object (not array) is rejected."""
    with pytest.raises(ValueError):
        csd.parse_dependencies('{"deps": []}')


def test_parse_dependencies_rejects_non_string_entry(csd):
    """A non-string entry in the array is rejected."""
    with pytest.raises(ValueError):
        csd.parse_dependencies('[42]')


def test_parse_dependencies_rejects_garbage_entry(csd):
    """An entry that is not a valid clause identifier is rejected."""
    with pytest.raises(ValueError):
        csd.parse_dependencies('["not-a-clause"]')


def test_parse_dependencies_rejects_lowercase_letter(csd):
    """A lowercase letter clause is rejected."""
    with pytest.raises(ValueError):
        csd.parse_dependencies('["a.7"]')


# ---- main -------------------------------------------------------------------


def _run_main(csd, tmp_path, *, deps=None, extra=None):
    """Run main() with run_oracle_call stubbed; return captured mock."""
    payload = json.dumps(deps if deps is not None else [])
    args = _args_with_lrm(tmp_path, *(extra or []))
    with patch(
        "compute_subclause_dependencies.run_oracle_call",
        return_value=payload,
    ) as mock_run:
        csd.main(args)
    return mock_run


def test_main_invokes_run_oracle_call(csd, tmp_path):
    """main() invokes the oracle Claude call exactly once."""
    mock_run = _run_main(csd, tmp_path)
    assert mock_run.call_count == 1


def test_main_passes_model_to_run_oracle_call(csd, tmp_path):
    """main() forwards --model to the oracle Claude call."""
    mock_run = _run_main(csd, tmp_path, extra=["--model", "haiku"])
    assert mock_run.call_args[1]["model"] == "haiku"


def test_main_prints_dependency_array(csd, tmp_path, capsys):
    """main() prints the dependency JSON array to stdout."""
    _run_main(csd, tmp_path, deps=["33.6.1", "33.4.1.5"])
    payload = json.loads(capsys.readouterr().out)
    assert payload == ["33.6.1", "33.4.1.5"]


def test_main_prints_empty_array_when_no_deps(csd, tmp_path, capsys):
    """main() prints an empty JSON array when the oracle returns none."""
    _run_main(csd, tmp_path)
    payload = json.loads(capsys.readouterr().out)
    assert payload == []


def test_main_logs_subclause_to_stderr(csd, tmp_path, capsys):
    """main() prints a one-line dependency-oracle banner to stderr."""
    _run_main(csd, tmp_path)
    assert "§33.4.1.5" in capsys.readouterr().err


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("compute_subclause_dependencies", run_name="__main__")
