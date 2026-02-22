"""Shared test helpers for split_tests unit tests."""

import split_tests


def make_test_block(
    name, prefix=None, clause=None, rationale=None, comments=None,
):
    """Shorthand factory for TestBlock."""
    return split_tests.TestBlock(
        suite_name="S",
        test_name=name,
        lines=[f"TEST(S, {name}) {{", "}"],
        preceding_comments=comments or [],
        prefix=prefix,
        clause=clause,
        rationale=rationale,
    )


def make_parsed_file(
    includes=None, using=None, ns=False, preamble=None, tests=None,
):
    """Shorthand factory for ParsedFile."""
    return split_tests.ParsedFile(
        includes=includes or ["#include <gtest/gtest.h>"],
        using_line=using,
        has_namespace_wrapper=ns,
        global_preamble=preamble or [],
        sections=[],
        all_tests=tests or [],
    )


def monkeypatch_paths(monkeypatch, tmp_path):
    """Stub out LRM_PATH and ARCH_PATH to missing files."""
    monkeypatch.setattr(
        split_tests, "LRM_PATH", tmp_path / "no.txt",
    )
    monkeypatch.setattr(
        split_tests, "ARCH_PATH", tmp_path / "no.md",
    )


def stub_classifier(monkeypatch, tmp_path, response):
    """Stub out LRM/ARCH paths and _call_claude for classify_tests."""
    monkeypatch_paths(monkeypatch, tmp_path)
    monkeypatch.setattr(
        split_tests, "_call_claude", lambda p: response,
    )
