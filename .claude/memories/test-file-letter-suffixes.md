---
name: test-file-letter-suffixes
description: When more than one unit test file covers a subclause, end every file in that family with a letter and reserve the bare name for a one-file subclause.
metadata:
  type: feedback
---

# Letter suffixes on split test files

When more than one unit test file covers the same subclause, end every file in that family with a letter: `test_simulator_subclause_11_04_11a.cpp`, `test_simulator_subclause_11_04_11b.cpp`, and so on. Reserve the unsuffixed name for a subclause that occupies exactly one file.

**Why:** A family of `…_11_04_11.cpp` plus `…_11_04_11a.cpp` is the shape to avoid, because the bare name reads as the whole of the subclause when it is really only the first part of it. Nothing enforces the convention; the value is that everyone makes the same choice.

**How to apply:** Letters run in content order, so `a` holds the cases that came first in the file the family was split from. When splitting a one-file subclause, rename the original to `a` rather than leaving it bare and starting the new file at `b`. Each file is its own CMake target, so splitting a file is two changes, not one: the rename, and the `add_unit_test(...)` lines in `test/CMakeLists.txt` -- the old name replaced by `a`, and a line added for `b`. `add_unit_test` names every test explicitly and globs nothing, so a new file that is never named is never built. Getting this wrong is expensive out of all proportion to the one line: a registered name with no file behind it fails at configure time, which takes the coverage library and every clang-tidy test shard down with it, so eighteen jobs go red and none of the messages names the cause except `assert-file-and-registration-sets-agree`, which reports both directions of the mismatch. That gate is a `sed` and two `comm` calls over sorted names, cheap enough to replay locally before pushing any change that adds, renames or removes a test file -- the one place worth stepping outside [verifying-through-ci](verifying-through-ci.md). Check the letter is free first, per [checking-for-the-letter-before-writing](checking-for-the-letter-before-writing.md), and stage the rename carefully, per [git-add-all-or-nothing-pathspecs](git-add-all-or-nothing-pathspecs.md).
