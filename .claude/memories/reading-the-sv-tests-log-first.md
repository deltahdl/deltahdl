---
name: reading-the-sv-tests-log-first
description: The sv-tests CI log already carries the tool's own output under every FAIL line, so a rejected file is diagnosed there.
metadata:
  type: project
---

# Reading the sv-tests log before anything else

Read the CI log before doing anything else with a failing sv-tests file.

**Why:** `print_reason` in `scripts/run_sv_tests/__init__.py` prints the tool's own output under every FAIL line, and its docstring gives the reason: "A line naming the file that failed says nothing about why it failed, so whoever picks the failure up has to run the tool over that file themselves to find out -- and working it out from the source instead is a reliable way to reach a confident wrong answer. The output was captured when the test ran; this puts it where the run can be read afterwards."

**How to apply:** A rejection, the subclause it names, a rejection under a clause other than the one the corpus tags, and an exit that rejected nothing all arrive that way, so a file that fails by being rejected needs nothing local at all. The one thing the log drops is the rest of a simulated run's stdout, which is what [the-sv-tests-build-exception](the-sv-tests-build-exception.md) covers.
