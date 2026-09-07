---
name: test-file-letter-suffixes
description: When more than one unit test file covers a subclause, end every file in that family with a letter and reserve the bare name for a one-file subclause.
metadata:
  type: feedback
---

# Letter suffixes on split test files

When more than one unit test file covers the same subclause, end every file in that family with a letter: `test_simulator_subclause_11_04_11a.cpp`, `test_simulator_subclause_11_04_11b.cpp`, and so on. Reserve the unsuffixed name for a subclause that occupies exactly one file.

**Why:** A family of `…_11_04_11.cpp` plus `…_11_04_11a.cpp` is the shape to avoid, because the bare name reads as the whole of the subclause when it is really only the first part of it. Nothing enforces the convention; the value is that everyone makes the same choice.

**How to apply:** Letters run in content order, so `a` holds the cases that came first in the file the family was split from. When splitting a one-file subclause, rename the original to `a` rather than leaving it bare and starting the new file at `b`. Each file is its own CMake target, so a rename means editing the `add_unit_test(...)` line in `test/CMakeLists.txt` to match; a target whose name no longer has a file behind it fails at configure time, not at build time. Check the letter is free first, per [checking-for-the-letter-before-writing](checking-for-the-letter-before-writing.md), and stage the rename carefully, per [git-add-all-or-nothing-pathspecs](git-add-all-or-nothing-pathspecs.md).
