---
name: test-driven-development
description: Write the tests first, in the same commit as the code they cover; pytest --cov-fail-under=100 enforces it for Python.
metadata:
  type: feedback
---

# Test-driven development

Write the tests first, then the production code that makes them pass.

**Why:** This repository does TDD, and it is enforced structurally. `.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over the `unit/` directory of every Python script and library module, so a commit that adds production code without matching unit tests fails on push, and there is no pull-request buffer to catch it first.

**How to apply:** For every change in `lib/python/`, `scripts/`, or their `test/` trees, write the unit test under `unit/` before the implementation, in the same commit. Each module also wants `integration/` and `e2e/` tests, though those are not coverage-gated. Test-first here means authoring order; the red and green observations can come from a local pytest run or from CI.
