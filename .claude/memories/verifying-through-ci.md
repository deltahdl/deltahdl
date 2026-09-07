---
name: verifying-through-ci
description: Never build locally and never run a local tool that CI also runs; push and read the run instead.
metadata:
  type: feedback
---

# Verifying through CI, not locally

Never build locally, and never run any local tool that CI also runs. The user set this rule on 2026-07-29.

**Why:** As the user put it: "CI does all checks. doing things locally costs Claude tokens. CI is free." Build, test, `clang-tidy`, the formatting check, the file-size cap, the assertions about suppressions and configuration files, the unit test registration checks, the copy-paste detectors and the whole Python side — pytest, the coverage gates, pylint, `mypy --strict`, `assert-one-assert-per-pytest` — all run in `.github/workflows/deltahdl.yml` and `.github/workflows/scripts.yml` for nothing.

**How to apply:** Make the edits, format, commit explicit paths, push, and read the run — see [reading-a-ci-run](reading-a-ci-run.md). Every smaller justification for running a gate locally has been used here and corrected:

- "Protect a CI cycle" — CI runs on free GitHub compute, in parallel, and there is no scarce resource to protect.
- "It is not a build or a test" — `clang-tidy` and the file-size cap are CI jobs like any other. A red run's `gh run view --log-failed` gives the same file/line/check list, for free, and one push verifies every file at once.
- "It reproduces the gate in 1.3 seconds" — the seconds are not the cost. The tokens spent reading its output are.
- "Local caught a regression, so it was worth it" — CI would have surfaced the same diff for nothing.

Do not build locally for a bug that only shows up while the simulator is running. An earlier version of this rule allowed exactly that, for coroutine, scheduler and event-watcher bugs, and the permission is gone: a local build always finds something, so it is easy to justify after the fact, and catching a regression is not evidence that the regression was invisible to CI. When a defect really does hide in run-time state, read the code and the clause instead of probing for it.

There are exactly two exceptions, and they are exceptions for different reasons. [clang-format-style-flag](clang-format-style-flag.md) rewrites files rather than judging them, so running it is part of authoring the change. [the-sv-tests-build-exception](the-sv-tests-build-exception.md) reads something the CI log does not carry, and is bounded by one named file.
