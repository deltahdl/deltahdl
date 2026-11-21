---
name: no-empty-test-files
description: "A test file with no TEST(...) block fails the assert-no-empty-test-files job, so a new lettered file is created only together with its first test"
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:51:02.559Z
---

# No empty test files

A test file under `test/src` holding no `TEST(...)` block fails the
`assert-no-empty-test-files` job (and an empty namespace fails
`clang-format` too), so a new lettered file is never committed as a
placeholder to fill later.

**Why:** a placeholder is empty when it is committed, whatever is written into
it later, so the push that carries it goes red.

**How to apply:** write the file's first test, and commit the file and its
`add_unit_test` line in the same commit as that test; see
[test-file-letter-suffixes](test-file-letter-suffixes.md) and [checking-for-the-letter-before-writing](checking-for-the-letter-before-writing.md).
