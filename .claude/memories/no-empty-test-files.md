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

**Why:** run 35497622647 went red on three placeholder files
(`test_elaborator_subclause_03_12_01b.cpp`, `20_06_02b.cpp`,
`test_simulator_subclause_26_03f.cpp`) that 36086db32 registered ahead of the
agents writing into them.

**How to apply:** give an agent the file's name and its `add_unit_test`
line to write, or write the file's first test yourself, and commit the file and
the CMake line in the same commit as that test; see
[[test-file-letter-suffixes]] and [[checking-for-the-letter-before-writing]].
