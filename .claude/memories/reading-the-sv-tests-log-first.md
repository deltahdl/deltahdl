---
name: reading-the-sv-tests-log-first
description: The sv-tests CI log already carries deltahdl's own output under every FAIL line, so a rejected file is diagnosed there.
metadata:
  type: project
---

# Reading the sv-tests log before anything else

Read the CI log before doing anything else with a failing sv-tests file.

**Why:** `print_reason` in `scripts/run_sv_tests/__init__.py` prints deltahdl's own output under every FAIL line. A line naming the file that failed says nothing about why it failed, and working the reason out from the source instead is a reliable way to reach a confident wrong answer; the output was captured when the test ran, and the log is where it can be read afterwards.

**How to apply:** A rejection, the subclause it names, a rejection under a clause other than the one the test's tag names, and an exit that rejected nothing all arrive that way, so a file that fails by being rejected needs nothing local at all. The one thing the log drops is the rest of a simulated run's stdout, which is what [the-sv-tests-build-exception](the-sv-tests-build-exception.md) covers.
