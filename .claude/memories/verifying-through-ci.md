---
name: verifying-through-ci
description: "Run locally only what shows a change works: its new tests, the files holding its rule's tests and the pre-push-checks skill over the touched files; every run across all of deltahdl is CI's, read after the push."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-09T21:00:00.000Z
---

# Checking locally, then verifying through CI

A change runs locally only as far as it takes to show that it works. Each new test is built and seen to fail, then pass, along with the test files that already hold the tests of the rule in hand. Before the push, `.claude/skills/pre-push-checks/check.sh` checks the touched files. Anything that runs across all of deltahdl belongs to CI: every unit test binary, clang-tidy beyond the touched files, and the integration, e2e and sv-tests runs. Push, then read the run for the verdict.

**Why:** A local run earns its time by answering whether a candidate fix works before it is settled on. A new test that fails for the wrong reason, a function over the statement limit or a subject that is too long would each cost a full CI cycle if found only after the push. A sweep of hundreds of test binaries, or of the whole lint pass, tells nothing that one CI run does not already tell with its jobs in parallel. It also holds the session idle through hours of building, since nothing else is done while a background command runs.

**How to apply:**

- **Red, then green.** Build and run each new test before writing its fix, and read why it fails: it must fail for the reason its issue names ([test-driven-development](test-driven-development.md)). Then write the fix and run the test again, with the files holding the rule's existing tests.
- **Before every push,** run the `pre-push-checks` skill over the committed change. It builds and runs the touched test files. Name as extra targets at most the files that hold the existing tests of the rule in hand, never a list of every target that might reach the changed code.
- **Scope.** CI runs all of these, and gives the verdict on them:
  - the other unit tests, and any changed line that only their tests reach;
  - clang-tidy beyond the touched files;
  - the sanitizer and gcc builds;
  - the e2e, integration and sv-tests runs;
  - the copy-paste detectors.

  Read the run, per [reading-a-ci-run](reading-a-ci-run.md), and fix a red one per [fixing-a-red-run](fixing-a-red-run.md).
- **Probes are allowed.** A defect may be probed by running a small design through `build-check/src/deltahdl`, built with `cmake --build build-check --target deltahdl`. What shows the defect is still a test that states it, pushed with its fix.
- **Long commands.** A build, a test run or a clang-tidy pass over many files runs in the background, per [long-running-commands-in-the-background](long-running-commands-in-the-background.md). Nothing else is done until it finishes, per [waiting-while-anything-runs-in-the-background](waiting-while-anything-runs-in-the-background.md).
