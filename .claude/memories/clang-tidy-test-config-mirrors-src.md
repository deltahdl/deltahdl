---
name: clang-tidy-test-config-mirrors-src
description: etc/clang_tidy/test_src_unit.yml is a full copy of etc/clang_tidy/src.yml and differs from it in five settings only; a change to one is made to both.
metadata:
  node_type: memory
  type: project
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:32.067Z
---

# The test clang-tidy configuration mirrors the source one

`etc/clang_tidy/test_src_unit.yml` governs `test/` and `lib/cpp/`, and `etc/clang_tidy/src.yml` governs `src/`. The workflow passes each by `-config-file=`, so each one is complete on its own and neither inherits from the other.

**Why:** A check or naming rule changed in one file and not the other holds the two tiers to different rules by accident. Only five differences are intended:

- `readability-function-size.LineThreshold` is 300 for tests, 200 for `src/`.
- `readability-function-size.StatementThreshold` is 100 for tests, 50 for `src/`.
- `readability-function-cognitive-complexity.IgnoreMacros` is true for tests only, because GoogleTest's `ASSERT_*` and `EXPECT_*` macros expand into branches that would count toward the score.
- `src.yml` disables `bugprone-command-processor`, because §20.17.1 of IEEE 1800-2023 has `$system` pass its argument to the C `system()` command processor, the one call the check forbids. The test tier keeps the check on.
- `HeaderFilterRegex` adds `lib/cpp` for tests. `lib/cpp` is test-tier code, and no `src/` file includes one of its headers.

**How to apply:** When a check, option or naming rule changes in either file, make the same change in the other in the same commit, unless it is one of the differences above. Neither file is ever weakened to get a run through, per [never-weakening-a-gate](never-weakening-a-gate.md).
