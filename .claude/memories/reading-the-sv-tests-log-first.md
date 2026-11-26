---
name: reading-the-sv-tests-log-first
description: "The sv-tests CI log already carries deltahdl's own output under every FAIL line, so a rejected file is diagnosed there."
metadata:
  node_type: memory
  type: project
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:50:43.901Z
---

# Reading the sv-tests log before anything else

Read the CI log before doing anything else with a failing sv-tests file.

**Why:** `print_reason` in `scripts/run_sv_tests/__init__.py` prints deltahdl's own output under every FAIL line. A line naming the file that failed says nothing about why it failed, and working the reason out from the source instead is a reliable way to reach a confident wrong answer; the output was captured when the test ran, and the log is where it can be read afterwards.

**How to apply:** A rejection, the subclause it names, a rejection under a clause other than the one the test's tag names, and an exit that rejected nothing all arrive that way, so a file that fails by being rejected needs nothing more. The one thing the log drops is the rest of a simulated run's stdout. A test that runs the file's source and states what it prints shows it, in the CI run of its push ([verifying-through-ci](verifying-through-ci.md)), and that test is what settles the case.
