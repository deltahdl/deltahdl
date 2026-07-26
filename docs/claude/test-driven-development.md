# Test-driven development

Write the tests first, then the production code that makes them pass. The
user stated "we do TDD", and it is enforced structurally:
`.github/workflows/scripts.yml` runs `pytest --cov-fail-under=100` over
the `unit/` directory of every Python script and library module, so a
commit that adds production code without matching unit tests fails on
push — and there is no pull-request buffer to catch it first.

For every change in `lib/python/`, `scripts/`, or their `test/` trees,
write the unit test under `unit/` before the implementation, in the same
commit. Each module also wants `integration/` and `e2e/` tests, though
those are not coverage-gated. Test-first here means authoring order, not a
local red-green loop: the red and green observations belong to CI, since
pytest is not run locally.
