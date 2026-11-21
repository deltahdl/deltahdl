---
name: test-driven-development
description: "Write the tests first; a Python test lands in the same commit as the code it covers, which pytest --cov-fail-under=100 enforces, and a C++ unit test lands with its fix, except for an lrm-tests issue, which lands tests alone."
metadata:
  node_type: memory
  type: feedback
  originSessionId: b425c181-0dc9-4105-9628-ad8462acdd57
  modified: 2026-11-21T02:54:11.668Z
---

# Test-driven development

Write the tests first, then the production code that makes them pass.

**Why:** This repository does TDD, and it is enforced structurally. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module, so a commit that adds production code without matching unit tests fails on push, and there is no pull-request buffer to catch it first.

**How to apply:** For every change in `lib/python/`, `scripts/`, or their `test/` trees, write the unit test under `unit/` before the implementation, in the same commit. Each module also wants `integration/` and `e2e/` tests, though those are not coverage-gated. Test-first is a local red-green loop: run the new test before the code it covers and read its failure, which has to be the one the change sets out to fix, then write the code and run it again — `pytest` for Python, and for C++ the unit test target built in `build-check/` — see [verifying-through-ci](verifying-through-ci.md). A C++ change follows the same order, its tests under `test/src/unit/` written and seen to fail before the src change, and the `pre-push-checks` skill runs before the push. A C++ unit test lands in the same commit as its src change, and no src line lands uncovered. Only an `lrm-tests` issue lands tests without a src change ([lrm-tests-issues-are-tests-only](lrm-tests-issues-are-tests-only.md)).
