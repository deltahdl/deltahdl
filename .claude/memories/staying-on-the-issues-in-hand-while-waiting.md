---
name: staying-on-the-issues-in-hand-while-waiting
description: "While a local build, test run or pre-push check runs, work only on the issues in hand, in ways its result cannot change and editing no tracked file; never take up another issue to fill the wait."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-09T09:59:28.991Z
---

# Staying on the issues in hand while waiting

A wait never changes what is being worked on. While a local build, a test run or the `pre-push-checks` skill runs in the background, the only work that goes on is work for the issues in hand that its result cannot change, and none of it edits, stages or commits a tracked file. No other issue is read, planned or tested until the issues in hand are pushed, their runs are clean and they are closed. When no such work is left, the turn ends and the notification resumes it.

**Why:** A CI run is only waited for so that attention stays on one piece of work ([waiting-while-a-ci-run-is-in-progress](waiting-while-a-ci-run-is-in-progress.md)), and a local wait is no different: a result that lands in the middle of another issue's design comes back to a session thinking about something else. The waits are short as well, since `check.sh` takes under about a minute once `build-check/` is built, so reading ahead gains almost nothing. And `check.sh` reads the working tree until it finishes, for formatting, the build, coverage line numbers and clang-tidy, so an edit made while it runs is checked in place of the commit.

**How to apply:**

- After starting the command, end the turn, or do only what the issues in hand need and the result cannot overturn, such as reading the clause their rule comes from.
- A case is ticked in its issue only after the test that shows it has passed, never while that test is still building or running.
- Edit no tracked file while a build or check runs. `check.sh` reports a commit or tracked edit made during its run.
- The next issue or group is read only once the loop's command names it, after the issues in hand have closed. See [long-running-commands-in-the-background](long-running-commands-in-the-background.md) and [verifying-through-ci](verifying-through-ci.md).
