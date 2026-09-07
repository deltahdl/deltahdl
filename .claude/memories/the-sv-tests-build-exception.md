---
name: the-sv-tests-build-exception
description: The one case for building locally — running the simulator over a single already-failing sv-tests file to see the stdout the CI log drops.
metadata:
  type: feedback
---

# The sv-tests build exception

Build the simulator and run it on a single sv-tests file to find out why that file fails. This is one of the two exceptions to [verifying-through-ci](verifying-through-ci.md).

**Why:** `run_test` scores a simulated file through `check_assertions`, which walks the `:assert:` lines and returns `Assertion failed: <expr>` for the first that does not hold; every other line the run printed is discarded on the way. When the failing assertion and its two values do not themselves say why they differ, the surrounding output is what says it, and running the file is the only way to see it. That gap is the whole of the exception, and closing it in `run_sv_tests` would end the exception rather than widen it.

**How to apply:** Read the log first, per [reading-the-sv-tests-log-first](reading-the-sv-tests-log-first.md) — most of the answer is already there. Then fetch the file, per [fetching-an-sv-tests-file](fetching-an-sv-tests-file.md), and run it from an isolated Debug build directory; `ninja src/deltahdl` rebuilds incrementally. A file passes when each `:assert:` line reports equal values. The exception covers one named file that a CI run has already reported failing. It does not cover running the suite, running anything under `test/`, or rebuilding to check whether the fix worked — verify the fix by pushing, like everything else.
