"""Shared test helpers for classify_test unit tests."""

from typing import Any

import pytest

import classify_test
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


__all__ = [
    "make_parsed_file",
    "make_test_block",
    "stub_classifier",
    "stub_side_effects",
    "stub_subprocess_failure",
    "stub_subprocess_success",
]


def make_test_block(
    name: str,
    prefix: str | None = None,
    clause: str | None = None,
    *,
    comments: list[str] | None = None,
    body: list[str] | None = None,
) -> Any:
    """Shorthand factory for TestBlock."""
    if body is None:
        lines = [f"TEST(S, {name}) {{", "}"]
    else:
        lines = [f"TEST(S, {name}) {{"] + body + ["}"]
    return classify_test.TestBlock(
        suite_name="S",
        test_name=name,
        lines=lines,
        preceding_comments=comments or [],
        prefix=prefix,
        clause=clause,
        rationale=None,
    )


def make_parsed_file(
    includes: list[str] | None = None,
    using: str | None = None,
    ns: bool = False,
    preamble: list[Any] | None = None,
    tests: list[Any] | None = None,
) -> Any:
    """Shorthand factory for ParsedFile."""
    return classify_test.ParsedFile(
        includes=includes or ["#include <gtest/gtest.h>"],
        using_line=using,
        has_namespace_wrapper=ns,
        global_preamble=preamble or [],
        section_preamble=[],
        all_tests=tests or [],
    )


def stub_side_effects(monkeypatch: pytest.MonkeyPatch) -> None:
    """Stub maybe_update_issue_status and commit_classification."""
    monkeypatch.setattr(
        classify_test, "maybe_update_issue_status",
        lambda args, tests, **kw: None,
    )
    monkeypatch.setattr(
        classify_test, "commit_classification",
        lambda *a, **kw: None,
    )


def stub_classifier(
    monkeypatch: pytest.MonkeyPatch,
    response: Any,
    stage: str = "parser",
) -> None:
    """Stub _call_claude and side-effect functions for _run tests."""

    def _fake_claude(
        _prompt: str, schema: str | None = None, **_kw: Any,
    ) -> Any:
        if schema and "pipeline_stage" in schema:
            return {"pipeline_stage": stage, "rationale": "r"}
        return response

    monkeypatch.setattr(classify_test, "_call_claude", _fake_claude)
    stub_side_effects(monkeypatch)
