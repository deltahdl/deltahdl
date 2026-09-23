---
name: verifying-through-ci
description: Never run a gate CI also runs; push and read the run instead. Local builds to investigate a defect are allowed.
metadata:
  type: feedback
---

# Verifying through CI, not locally

Never run locally a tool that CI also runs; push and read the run instead.

**Why:** CI does all the checks, for free, while doing them locally costs tokens. Build, test, `clang-tidy`, the formatting check, the file-size cap, the assertions about suppressions and configuration files, the unit test registration checks, the copy-paste detectors and the whole Python side — pytest, the coverage gates, pylint, `mypy --strict`, `assert-one-assert-per-pytest` — all run in `.github/workflows/deltahdl.yml` and `.github/workflows/scripts.yml` for nothing.

**How to apply:** Make the edits, format, commit explicit paths, push, and read the run — see [reading-a-ci-run](reading-a-ci-run.md). Each of these smaller justifications for running a gate locally is wrong:

- "Protect a CI cycle" — CI runs on free GitHub compute, in parallel, and there is no scarce resource to protect.
- "It is not a build or a test" — `clang-tidy` and the file-size cap are CI jobs like any other. A red run's `gh run view --log-failed` gives the same file/line/check list, for free, and one push verifies every file at once.
- "It reproduces the gate in 1.3 seconds" — the seconds are not the cost. The tokens spent reading its output are.
- "Local caught a regression, so it was worth it" — CI would have surfaced the same diff for nothing.

Building locally to investigate is allowed. A Debug build of `deltahdl` in the scratchpad, run over small repro sources or an instrumented copy of a library such as UVM, is how to find where a run-time defect lives and to check that a fix changes the repro's output. What is still not done locally is the gate list above: the unit test binaries, `clang-tidy`, the size caps, pytest and the rest are still verified by pushing and reading the run.

Apart from investigation, there are two exceptions, and they are exceptions for different reasons. [clang-format-style-flag](clang-format-style-flag.md) rewrites files rather than judging them, so running it is part of authoring the change. [the-sv-tests-build-exception](the-sv-tests-build-exception.md) reads something the CI log does not carry, and is bounded by one named file.
