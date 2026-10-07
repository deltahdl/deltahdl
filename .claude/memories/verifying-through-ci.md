---
name: verifying-through-ci
description: "Keep local work to what CI has no way to perform; everything else, a build or a probe of a defect included, is pushed and read from the run."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 80ac19af-0e3c-46db-9fa6-1642c305f31d
  modified: 2026-10-03T00:59:43.573Z
---

# Verifying through CI, not locally

Local work is confined to the steps CI has no way to perform. Whatever a CI job is able to do is pushed and read from the run instead.

**Why:** CI runs on GitHub's compute for free, while running locally costs tokens and session time. The run's own jobs already cover a great deal, all in `.github/workflows/deltahdl.yml` and `.github/workflows/scripts.yml`:

- the build and the unit, e2e and sv-tests runs
- `clang-tidy`, the formatting check and the file-size cap
- the assertions about suppressions and configuration files, and the unit test registration checks
- the copy-paste detectors
- the whole Python side: pytest, the coverage gates, pylint, `mypy --strict` and `assert-one-assert-per-pytest`

What a run does not do yet can still be made to run there: a test written for it, or a step added to a workflow.

**How to apply:** Make the edits, format, commit explicit paths, push, and read the run, per [reading-a-ci-run](reading-a-ci-run.md). Do not build `deltahdl` or a test binary locally, do not run a probe design through a local binary, and do not keep a local coverage or regression build. A defect is shown by a test that states it, pushed with its fix, and the run says whether the fix holds. Each of these justifications for a local run is wrong:

- "It is only an investigation, not a gate." CI can run the investigation, so it is not an exception.
- "Protect a CI cycle." CI runs in parallel, and there is no scarce resource to protect.
- "It reproduces the gate in 1.3 seconds." The seconds are not the cost; the tokens spent reading its output are.
- "Local caught a regression, so it was worth it." CI would have surfaced the same diff for nothing.
- "Build every target once the fixes are in, to see the push compiles." That is the build job's check.
- "Run the new test to see it pass, or to see it fail first." That is the unit test job.
- "A pre-push regression script." Rebuilding the unit tests, running every binary, collecting coverage and replaying the e2e sources are the CI jobs under another name.

One step CI has no way to perform is [clang-format-style-flag](clang-format-style-flag.md), which rewrites the files and so is how the committed bytes come to exist. Another is reading the LRM, which is copyrighted and kept only on this machine, as in [zooming-on-a-formula](zooming-on-a-formula.md).
