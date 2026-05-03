"""Unit tests for _run flow in classify_test."""

import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace
from typing import Any

import pytest

from ._main_helpers import (
    make_input_file as _make_input_file,
    parser_response as _parser_response,
    run_args as _run_args,
)

M = ModuleType
C = pytest.CaptureFixture[str]
P = pytest.MonkeyPatch


# ---- _run ------------------------------------------------------------------


def test_run_file_not_found(tmp_path: Path, ct: M) -> None:
    """Exits when input file does not exist."""
    _run = getattr(ct, "_run")
    args = _run_args(tmp_path, file=str(tmp_path / "missing.cpp"))
    with pytest.raises(SystemExit):
        _run(args)


def test_run_no_test_blocks(tmp_path: Path, ct: M) -> None:
    """Exits when file has no TEST blocks."""
    _run = getattr(ct, "_run")
    f = tmp_path / "empty.cpp"
    f.write_text(
        "#include <gtest/gtest.h>\n\nint x = 0;\n",
        encoding="utf-8",
    )
    args = _run_args(tmp_path, file=str(f))
    with pytest.raises(SystemExit):
        _run(args)


def test_run_test_not_found(tmp_path: Path, ct: M) -> None:
    """Exits when --test names a test not in the file."""
    _run = getattr(ct, "_run")
    _make_input_file(tmp_path)
    args = _run_args(tmp_path, test="NoSuchTest")
    with pytest.raises(SystemExit):
        _run(args)


def test_run_dry_run_shows_target(tmp_path: Path, monkeypatch: P,
                                  capsys: C, ct: M, ct_helpers: M) -> None:
    """Dry-run output shows the target filename."""
    _run = getattr(ct, "_run")
    _make_input_file(tmp_path)
    ct_helpers.stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "test_parser_clause_06_01.cpp" in capsys.readouterr().out


def test_run_prints_action_moved(tmp_path: Path, monkeypatch: P,
                                 capsys: C, ct: M, ct_helpers: M) -> None:
    """_run prints action line when test is moved."""
    _run = getattr(ct, "_run")
    _make_input_file(tmp_path)
    ct_helpers.stub_classifier(monkeypatch, _parser_response())
    args = _run_args(tmp_path, dry_run=True)
    _run(args)
    assert "Action: Moved to test_parser_clause_06_01.cpp" in capsys.readouterr().out


def _setup_live_run(ct: M, ct_helpers: M, tmp_path: Path, monkeypatch: P) -> SimpleNamespace:
    """Create input file, cmake, and stub classifier for a live run."""
    _make_input_file(tmp_path)
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        "# header\nadd_unit_test(test_input)\n",
        encoding="utf-8",
    )
    ct_helpers.stub_classifier(monkeypatch, _parser_response())
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    return _run_args(tmp_path)


def test_run_live_updates_cmake(tmp_path: Path, monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """Live run updates CMakeLists.txt with new entry."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "test_parser_clause_06_01" in \
        (tmp_path / "CMakeLists.txt").read_text()


def test_run_live_prints_cmake_update(tmp_path: Path, monkeypatch: P,
                                      capsys: C, ct: M, ct_helpers: M) -> None:
    """Live run prints CMakeLists.txt update message."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "Updated `CMakeLists.txt`" in capsys.readouterr().out


def test_run_live_prints_cmake_updating(tmp_path: Path, monkeypatch: P,
                                        capsys: C, ct: M, ct_helpers: M) -> None:
    """Live run prints 'Updating' with rationale before the update."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    out = capsys.readouterr().out
    assert "Updating `CMakeLists.txt` because" in out


def test_run_live_delete_prints_message(tmp_path: Path, monkeypatch: P,
                                        capsys: C, ct: M, ct_helpers: M) -> None:
    """Live run prints delete message when source file is removed."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    out = capsys.readouterr().out
    assert "Deleting test_input.cpp because all its tests" \
           " were moved elsewhere" in out


def test_run_live_merge_writes_test(tmp_path: Path, monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """Live run merging into existing file writes the test."""
    _run = getattr(ct, "_run")
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "TEST(Parsing, T)" in \
        (tmp_path / "test_parser_clause_06_01.cpp").read_text()


def _setup_live_merge(ct: M, ct_helpers: M, tmp_path: Path, monkeypatch: P) -> SimpleNamespace:
    """Create existing clause file and set up a live merge run."""
    (tmp_path / "test_parser_clause_06_01.cpp").write_text(
        "// \u00a76.1\n\n#include <gtest/gtest.h>\n\n"
        "namespace {\n\nTEST(S, Old) {\n}\n\n}  // namespace\n",
        encoding="utf-8",
    )
    return _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)


def test_run_live_merge_prints_test_name(tmp_path: Path, monkeypatch: P,
                                         capsys: C, ct: M, ct_helpers: M) -> None:
    """Live merge message includes the test name."""
    _run = getattr(ct, "_run")
    args = _setup_live_merge(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "Merging test T into" in capsys.readouterr().out


def test_run_live_merge_prints_rationale(tmp_path: Path, monkeypatch: P,
                                         capsys: C, ct: M, ct_helpers: M) -> None:
    """Live merge message includes a rationale."""
    _run = getattr(ct, "_run")
    args = _setup_live_merge(ct, ct_helpers, tmp_path, monkeypatch)
    _run(args)
    assert "because" in capsys.readouterr().out

def _mixed_classifier(prompt: str, schema: str | None = None, **_kw: Any) -> dict[str, Any]:
    """Return different classifications based on which test is in prompt."""
    if schema and "pipeline_stage" in schema:
        return {"pipeline_stage": "parser", "rationale": "r"}
    if "Stay" in prompt:
        if schema and "non_lrm_topic" in schema:
            return {"non_lrm_topic": "aig", "rationale": "r",
                    "suite_name": "AigGraph", "test_name": "Stay"}
        return {"clause": "non-lrm", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "Stay"}
    return {"clause": "6.1", "rationale": "r",
            "suite_name": "Parsing", "test_name": "Move"}


def _run_live_non_lrm(ct: M, tmp_path: Path, monkeypatch: P, *, src_body: str,
                      test: str = "T") -> None:
    """Write source and run live pipeline.

    Callers must stub _call_claude and side effects before calling.
    """
    _run = getattr(ct, "_run")
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(src_body, encoding="utf-8")
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(
        f"# header\nadd_unit_test({src.stem})\n", encoding="utf-8",
    )
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    _run(_run_args(tmp_path, file=str(src), test=test))


def _self_named_classifier(_prompt: str, schema: str | None = None, **_kw: Any) -> dict[str, Any]:
    """Classify single test as non-lrm with topic aig."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "T"}
    return {"clause": "non-lrm", "rationale": "r",
            "suite_name": "AigGraph", "test_name": "T"}


def test_run_prints_action_kept(tmp_path: Path, monkeypatch: P,
                                capsys: C, ct: M, ct_helpers: M) -> None:
    """_run prints action line when test is kept in the same file."""
    monkeypatch.setattr(ct, "_call_claude", _self_named_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body="#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
    )
    assert "Action: Kept in the same file but renamed suite to AigGraph" in capsys.readouterr().out


def test_run_live_self_named(tmp_path: Path, monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """Source file already in correct location is left untouched."""
    monkeypatch.setattr(ct, "_call_claude", _self_named_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body="#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


def _no_rename_classifier(_prompt: str, schema: str | None = None, **_kw: Any) -> dict[str, Any]:
    """Classify single test as non-lrm/aig without renaming."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "S", "test_name": "T"}
    return {"clause": "non-lrm", "rationale": "r",
            "suite_name": "S", "test_name": "T"}


def test_run_live_self_named_no_rename(tmp_path: Path, monkeypatch: P,
                                       ct: M, ct_helpers: M) -> None:
    """Source-is-target with no rename leaves file intact."""
    monkeypatch.setattr(ct, "_call_claude", _no_rename_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body="#include <gtest/gtest.h>\n\n"
        "TEST(S, T) {\n  auto r = Parse(src);\n}\n",
    )
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


_MIXED_BODY = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Stay) {\n  auto r = Parse(src);\n}\n"
    "TEST(S, Move) {\n  auto r = Parse(src);\n}\n"
)


def test_run_live_mixed_keeps_source(tmp_path: Path, monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """Source is rewritten with only the staying tests."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Stay" in src


def test_run_live_mixed_removes_moved_from_source(tmp_path: Path, monkeypatch: P,
                                                  ct: M, ct_helpers: M) -> None:
    """Moved tests are removed from the source file."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Move" not in src


def test_run_live_mixed_creates_new_file(tmp_path: Path, monkeypatch: P,
                                         ct: M, ct_helpers: M) -> None:
    """Moved tests are written to a new clause file."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    assert (tmp_path / "test_parser_clause_06_01.cpp").exists()


def test_run_live_mixed_keeps_cmake_entry(tmp_path: Path, monkeypatch: P,
                                          ct: M, ct_helpers: M) -> None:
    """Source kept in CMakeLists.txt when source_is_target."""
    monkeypatch.setattr(ct, "_call_claude", _mixed_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(
        ct, tmp_path, monkeypatch,
        src_body=_MIXED_BODY, test="Move",
    )
    cmake = (tmp_path / "CMakeLists.txt").read_text()
    assert "test_non_lrm_aig" in cmake


_DUP_BODY_TWO = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Keep) {\n  auto r = Parse(src);\n}\n"
    "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
)

_DUP_BODY_ONE = (
    "#include <gtest/gtest.h>\n\n"
    "TEST(S, Dup) {\n  auto r = Parse(src);\n}\n"
)


def _run_live_dedup(ct: M, ct_helpers: M, tmp_path: Path, monkeypatch: P, src_body: str) -> None:
    """Pre-create variant with Dup, stub externals, and run live pipeline."""
    variant = tmp_path / "test_non_lrm_aig_a.cpp"
    variant.write_text(
        "#include <gtest/gtest.h>\n\nTEST(S, Dup) {\n  auto r = Parse(src);\n}\n",
        encoding="utf-8",
    )
    monkeypatch.setattr(ct, "_call_claude", _self_named_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(ct, tmp_path, monkeypatch, src_body=src_body, test="Dup")


def test_run_live_removes_duplicates_from_source(tmp_path: Path, monkeypatch: P,
                                                 ct: M, ct_helpers: M) -> None:
    """Live run rewrites source to remove tests that already exist elsewhere."""
    _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, _DUP_BODY_TWO)
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Dup" not in src


def test_run_live_dedup_only_test_rewrites_source(tmp_path: Path, monkeypatch: P,
                                                  ct: M, ct_helpers: M) -> None:
    """Source with only the duplicate test is rewritten empty."""
    _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, _DUP_BODY_ONE)
    assert (tmp_path / "test_non_lrm_aig.cpp").exists()


def test_run_live_keeps_non_duplicates_when_removing(tmp_path: Path,
        monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """Live run keeps non-duplicate tests when removing duplicates."""
    _run_live_dedup(ct, ct_helpers, tmp_path, monkeypatch, _DUP_BODY_TWO)
    src = (tmp_path / "test_non_lrm_aig.cpp").read_text()
    assert "Keep" in src


def _rewrite_source_fixture(ct: M, ct_helpers: M, tmp_path: Path) -> Any:
    """Create parsed file, groups, and temp file for rewrite tests."""
    t = ct_helpers.make_test_block(
        "T", prefix="test_parser_", clause="6.1",
    )
    parsed = ct.ParsedFile(
        includes=["#include <gtest/gtest.h>"],
        using_line=None, has_namespace_wrapper=True,
        global_preamble=[], section_preamble=[],
        all_tests=[t],
    )
    groups = {("test_parser_", "6.1"): [t]}
    f = tmp_path / "test_parser_clause_06_01.cpp"
    f.write_text("old", encoding="utf-8")
    return parsed, groups, f


def test_rewrite_source_writes_file(tmp_path: Path, ct: M, ct_helpers: M) -> None:
    """_rewrite_source writes the file with staying tests."""
    parsed, groups, f = _rewrite_source_fixture(ct, ct_helpers, tmp_path)
    getattr(ct, "_rewrite_source")(
        f, groups, parsed, {}, "test_parser_clause_06_01",
    )
    assert "TEST" in f.read_text()


def test_update_source_calls_rewrite(tmp_path: Path, ct: M, ct_helpers: M) -> None:
    """_update_source delegates to _rewrite_source when source_is_target."""
    parsed, groups, f = _rewrite_source_fixture(ct, ct_helpers, tmp_path)
    result = getattr(ct, "_update_source")(f, parsed, {
        "suite": "S", "test": "T", "groups": groups,
        "titles": {}, "stem": "test_parser_clause_06_01",
        "source_is_target": True,
    })
    assert result == 1


# ---- _run with --issue -----------------------------------------------------


def _setup_maybe_update_test(ct: M, ct_helpers: M, tmp_path: Path, monkeypatch: P) -> Any:
    """Set up a live run and capture maybe_update_issue_status calls."""
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    monkeypatch.setattr(ct, "commit_classification", lambda _ctx: "abc123")
    called = []
    gh = __import__("classify_test._github", fromlist=["_github"])
    monkeypatch.setattr(
        gh, "maybe_update_issue_status",
        lambda *_a, **_kw: called.append(True),
    )
    return getattr(ct, "_run"), called, args


def test_run_with_issue_calls_maybe_tick(tmp_path: Path, monkeypatch: P,
                                         ct: M, ct_helpers: M) -> None:
    """_run with --issue calls maybe_update_issue_status."""
    _run, called, args = _setup_maybe_update_test(
        ct, ct_helpers, tmp_path, monkeypatch,
    )
    args.issue = 42
    args.organization = "myorg"
    args.repo = "myrepo"
    _run(args)
    assert len(called) == 1


def test_run_without_issue_skips_maybe_tick(tmp_path: Path, monkeypatch: P,
                                            ct: M, ct_helpers: M) -> None:
    """_run without --issue skips maybe_update_issue_status."""
    _run, called, args = _setup_maybe_update_test(
        ct, ct_helpers, tmp_path, monkeypatch,
    )
    _run(args)
    assert len(called) == 0


def test_run_dry_run_skips_issue_update(tmp_path: Path, monkeypatch: P,
                                        ct: M, ct_helpers: M) -> None:
    """_run with --dry-run does not update the issue."""
    _run, called, args = _setup_maybe_update_test(
        ct, ct_helpers, tmp_path, monkeypatch,
    )
    args.dry_run = True
    args.issue = 42
    args.organization = "myorg"
    args.repo = "myrepo"
    _run(args)
    assert len(called) == 0


def test_run_no_commit_skips_commit(tmp_path: Path, monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """_run with no_commit=True does not call commit_classification."""
    _run = getattr(ct, "_run")
    args = _setup_live_run(ct, ct_helpers, tmp_path, monkeypatch)
    args.no_commit = True
    called = []
    monkeypatch.setattr(
        ct, "commit_classification",
        lambda _ctx: called.append(True),
    )
    _run(args)
    assert not called


# ---- rename in place -------------------------------------------------------


def _rename_classifier(_prompt: str, schema: str | None = None, **_kw: Any) -> dict[str, Any]:
    """Classify single test as non-lrm:aig and rename to Renamed."""
    if schema and "non_lrm_topic" in schema:
        return {"non_lrm_topic": "aig", "rationale": "r",
                "suite_name": "AigGraph", "test_name": "Renamed"}
    return {"clause": "non-lrm", "rationale": "r",
            "suite_name": "AigGraph", "test_name": "Renamed"}

_RENAME_BODY = ("#include <gtest/gtest.h>\n\n"
                "TEST(S, T) {\n  auto r = Parse(src);\n}\n")


def _run_rename(ct: M, ct_helpers: M, tmp_path: Path, monkeypatch: P) -> None:
    """Run live non-lrm pipeline with the rename classifier."""
    monkeypatch.setattr(ct, "_call_claude", _rename_classifier)
    ct_helpers.stub_side_effects(monkeypatch)
    _run_live_non_lrm(ct, tmp_path, monkeypatch, src_body=_RENAME_BODY)


def test_run_rename_in_place_rewrites_file(tmp_path: Path, monkeypatch: P,
                                           ct: M, ct_helpers: M) -> None:
    """Rename-in-place rewrites the source file with the new test name."""
    _run_rename(ct, ct_helpers, tmp_path, monkeypatch)
    assert "TEST(AigGraph, Renamed)" in \
        (tmp_path / "test_non_lrm_aig.cpp").read_text()


def test_run_rename_in_place_removes_old_name(tmp_path: Path, monkeypatch: P,
                                              ct: M, ct_helpers: M) -> None:
    """Rename-in-place removes the old TEST macro name from the file."""
    _run_rename(ct, ct_helpers, tmp_path, monkeypatch)
    assert "TEST(S, T)" not in \
        (tmp_path / "test_non_lrm_aig.cpp").read_text()


def _run_rename_commit(ct: M, tmp_path: Path, monkeypatch: P) -> list[Any]:
    """Capture commits from the rename pipeline."""
    monkeypatch.setattr(ct, "_call_claude", _rename_classifier)
    committed: list[Any] = []
    monkeypatch.setattr(ct, "commit_classification", committed.append)
    _run_live_non_lrm(ct, tmp_path, monkeypatch, src_body=_RENAME_BODY)
    return committed


def test_run_rename_in_place_commits(tmp_path: Path, monkeypatch: P, ct: M) -> None:
    """Rename-in-place calls commit_classification."""
    assert len(_run_rename_commit(ct, tmp_path, monkeypatch)) == 1


def test_run_commit_includes_action(tmp_path: Path, monkeypatch: P, ct: M) -> None:
    """Commit message includes the action remark."""
    committed = _run_rename_commit(ct, tmp_path, monkeypatch)
    assert "action" in committed[0]


def test_run_rename_in_place_no_commit(tmp_path: Path, monkeypatch: P, ct: M) -> None:
    """Rename-in-place with no_commit=True skips commit_classification."""
    monkeypatch.setattr(ct, "_call_claude", _rename_classifier)
    committed: list[Any] = []
    monkeypatch.setattr(ct, "commit_classification", committed.append)
    src = tmp_path / "test_non_lrm_aig.cpp"
    src.write_text(_RENAME_BODY, encoding="utf-8")
    cmake = tmp_path / "CMakeLists.txt"
    cmake.write_text(f"# header\nadd_unit_test({src.stem})\n",
                     encoding="utf-8")
    monkeypatch.setattr(ct, "CMAKE_PATH", cmake)
    args = _run_args(tmp_path, file=str(src), no_commit=True)
    getattr(ct, "_run")(args)
    assert not committed


def test_run_against_none_skips(tmp_path: Path, monkeypatch: P, ct: M, ct_helpers: M) -> None:
    """_run returns early when classify_test_block returns None."""
    _make_input_file(tmp_path)
    ct_helpers.stub_classifier(monkeypatch, {
        "clause": "none", "rationale": "r",
        "suite_name": "S", "test_name": "T",
    })
    args = _run_args(tmp_path, against="23.2.1")
    getattr(ct, "_run")(args)
    assert (tmp_path / "test_input.cpp").exists()


def _stub_main(monkeypatch: P, ct: M, run_fn: Any) -> None:
    """Stub _parse_args and _run for main() tests."""
    monkeypatch.setattr(ct, "_run", run_fn)
    monkeypatch.setattr(ct, "_parse_args", lambda: SimpleNamespace(
        file="x", output_dir="/tmp", dry_run=True, lrm="/lrm.txt",
        issue=None, organization=None, repo=None,
    ))


def test_main(monkeypatch: P, ct: M) -> None:
    """main calls _run with parsed args."""
    ran = [False]
    _stub_main(monkeypatch, ct, lambda _: ran.__setitem__(0, True))
    ct.main()
    assert ran[0] is True


def test_main_enables_line_buffering(monkeypatch: P, ct: M) -> None:
    """main reconfigures stdout to line-buffered mode."""
    configured = []
    monkeypatch.setattr(
        sys.stdout, "reconfigure",
        lambda **kw: configured.append(kw),
    )
    _stub_main(monkeypatch, ct, lambda _: None)
    ct.main()
    assert any(k.get("line_buffering") for k in configured)
