---
name: verifying-through-ci
description: "Check locally what a change touches before pushing it, with the pre-push-checks skill; the CI run after the push still gives the verdict over all of deltahdl."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 80ac19af-0e3c-46db-9fa6-1642c305f31d
  modified: 2026-11-09T08:18:26.630Z
---

# Checking locally, then verifying through CI

Before a push, the change is built and checked locally over what it touches: the test files it adds or edits are built and run, the changed src lines are read for coverage, and clang-tidy, clang-format and the file-size cap run over the touched files. `.claude/skills/pre-push-checks/check.sh` does all of it in one command, and the push waits until it passes. After the push, the CI run is read as before and gives the verdict over everything.

**Why:** Pushing unchecked work and reading the run cost a full CI cycle, about an hour, for each mistake a local check finds in minutes. A function one statement over the limit, a branch no test took or a subject too long each sent a push back red and needed a push of its own to fix. A local build also shows a new test's first failure, so a test that fails for a reason outside the rule in hand is seen before the fix is designed around it.

**How to apply:**

- **Red, then green.** Build and run each new test before writing its fix, and read why it fails: it must fail for the reason its issue names ([test-driven-development](test-driven-development.md)). Then write the fix and run the test again.
- **Before every push,** run the `pre-push-checks` skill over the committed change, naming any other test targets that reach the changed code, and fix what it reports.
- **Scope.** Keep the local work to what the change touches. The full unit suite of over three thousand binaries, the sanitizer and gcc builds, the e2e, integration and sv-tests runs and the copy-paste detectors stay CI's, and so does the verdict: read the run, per [reading-a-ci-run](reading-a-ci-run.md), and fix a red one per [fixing-a-red-run](fixing-a-red-run.md).
- **Probes are allowed.** A defect may be probed by running a small design through `build-check/src/deltahdl`, built with `cmake --build build-check --target deltahdl`, but what shows the defect is still a test that states it, pushed with its fix.
- **Long commands.** A build, a test run or a clang-tidy pass over many files runs in the background, per [long-running-commands-in-the-background](long-running-commands-in-the-background.md), and nothing else is done until it finishes, per [waiting-while-anything-runs-in-the-background](waiting-while-anything-runs-in-the-background.md).
