---
name: overwritten-test-file
description: A `>` redirect onto an existing letter-suffixed test file destroyed the ten cases commit c30f5c7ce had put there.
metadata:
  type: project
---

# The split that destroyed ten test cases

On 2026-07-26 a split of `test_parser_annex_a_09_03.cpp` wrote its second half straight to `test_parser_annex_a_09_03a.cpp` with a `>` redirect. That file already existed — commit `c30f5c7ce` had created it — and the redirect destroyed the ten test cases in it.

Nothing caught this until CMake refused the duplicate `add_unit_test` line, and by then the loss was committed.

Supports [test-file-letter-suffixes](../conventions/test-file-letter-suffixes.md).
