"""Shared test helpers for classify_test unit tests."""

import subprocess
from unittest.mock import MagicMock

import classify_test


def make_test_block(
    name, prefix=None, clause=None, *,
    comments=None, body=None,
):
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
    includes=None, using=None, ns=False,
    preamble=None, tests=None,
):
    """Shorthand factory for ParsedFile."""
    return classify_test.ParsedFile(
        includes=includes or ["#include <gtest/gtest.h>"],
        using_line=using,
        has_namespace_wrapper=ns,
        global_preamble=preamble or [],
        section_preamble=[],
        all_tests=tests or [],
    )


def stub_subprocess_failure(monkeypatch):
    """Stub subprocess.run to return a failure result."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )


def stub_classifier(monkeypatch, response):
    """Stub _call_claude and maybe_tick_issue_checkbox for _run tests."""
    monkeypatch.setattr(
        classify_test, "_call_claude",
        lambda p, schema=None: response,
    )
    monkeypatch.setattr(
        classify_test, "maybe_tick_issue_checkbox",
        lambda args, tests: None,
    )
