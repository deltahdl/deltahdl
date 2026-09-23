---
name: no-empty-test-files
description: "A test file with no TEST(...) block fails the assert-no-empty-test-files job, so a new lettered file is created only together with its first test"
metadata:
  type: feedback
---

# No empty test files

A test file under `test/src` holding no `TEST(...)` block fails the
`assert-no-empty-test-files` job (and an empty namespace fails
`clang-format` too), so a new lettered file is never committed as a
placeholder for an agent to fill.

**Why:** a placeholder is empty when it is committed, whatever an agent will
write into it later, so the push that carries it goes red.

**How to apply:** give an agent the file's name and its `add_unit_test`
line to write, or write the file's first test yourself, and commit the file and
the CMake line in the same commit as that test; see
[[test-file-letter-suffixes]] and [[checking-for-the-letter-before-writing]].
