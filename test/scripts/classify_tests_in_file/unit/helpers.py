"""Shared test helpers for classify_tests_in_file unit tests."""

import classify_tests_in_file


def make_test_block(
    name, prefix=None, clause=None, rationale=None, comments=None,
    body=None,
):
    """Shorthand factory for TestBlock."""
    if body is None:
        lines = [f"TEST(S, {name}) {{", "}"]
    else:
        lines = [f"TEST(S, {name}) {{"] + body + ["}"]
    return classify_tests_in_file.TestBlock(
        suite_name="S",
        test_name=name,
        lines=lines,
        preceding_comments=comments or [],
        prefix=prefix,
        clause=clause,
        rationale=rationale,
    )


def make_parsed_file(
    includes=None, using=None, ns=False,
    preamble=None, tests=None,
):
    """Shorthand factory for ParsedFile."""
    return classify_tests_in_file.ParsedFile(
        includes=includes or ["#include <gtest/gtest.h>"],
        using_line=using,
        has_namespace_wrapper=ns,
        global_preamble=preamble or [],
        section_preamble=[],
        all_tests=tests or [],
    )


def stub_classifier(monkeypatch, response):
    """Stub _call_claude for classify_tests."""
    monkeypatch.setattr(
        classify_tests_in_file, "_call_claude",
        lambda p, schema=None: response,
    )
