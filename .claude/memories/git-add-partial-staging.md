---
name: git-add-partial-staging
description: Naming a removed path to `git add` staged nothing, and commit c45398c25 carried a bare 997-line deletion to main.
metadata:
  type: project
---

# The split that committed only its deletion

Commit `c45398c25` was to split `test/src/unit/test_simulator_subclause_32_09.cpp` in two under #3157. The deletion of the original was already staged, and naming that path to `git add` beside the two files replacing it staged neither of them, because `git add` stages none of its pathspecs when any one matches nothing on disk.

The commit therefore carried a bare 997-line deletion to `main`, where `test/CMakeLists.txt` then named a source file that was gone. `6e63b7c56` added what the split was meant to carry.

Supports [staging-explicit-paths](../rules/staging-explicit-paths.md).
