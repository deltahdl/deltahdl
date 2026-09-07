---
name: unique-test-names
description: Declare each fully-qualified gtest name Suite.Name in one file only; a CI job fails on any duplicate.
metadata:
  type: project
---

# One declaration per fully-qualified test name

Declare each `Suite.Name` in one file only. The assert-no-duplicate-test-names job fails on any name declared more than once.

**Why:** A gtest case is identified by `Suite.Name`, and neither the compiler nor `gtest_discover_tests` objects when two files declare the same one. Each unit test source in `test/src/unit/` compiles into an executable of its own, and every case is registered into CTest under the bare `Suite.Name` — no binary, no path, nothing else to tell one from another. So `ctest -R Suite.Name` and `--gtest_filter` select every copy, and a failure report names the suite and the test but not the file that broke.

**How to apply:** Check the name before writing it. Where two files legitimately cover one rule, keep both and rename — see [renaming-rather-than-deleting-a-duplicate-test](renaming-rather-than-deleting-a-duplicate-test.md).
