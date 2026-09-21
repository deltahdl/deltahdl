---
name: waiting-while-a-ci-run-is-in-progress
description: "The autopilot reminder \"do not do anything but wait while a workflow is running\" means a GitHub Actions run, not the Workflow tool; no diagnosis, editing or committing while one is in progress."
metadata: 
  node_type: memory
  type: feedback
  originSessionId: dfd37fb2-9883-4abd-b54c-97199f0eba65
  modified: 2026-09-21T23:29:28.339Z
---

# Waiting while a CI run is in progress

While any CI run for a pushed commit is in progress -- any workflow under .github/workflows, deltahdl.yml, scripts.yml, documentation.yml or another -- do nothing but wait for it: no probing of the failing file, no edits, no local commits. The user set this on 2026-09-21, and corrected a first record that named deltahdl.yml alone.

**Why:** The standing reminder "Do not do anything but wait while a workflow is running" was read as naming the Workflow tool (multi-agent orchestration) and diagnosis carried on beside a running run; the user asked whether the reminder did not say to wait. A run's findings decide the next step, and work done before they land is done on a guess about them.

**How to apply:** After a push, arm the monitor and stop. Read the run when it completes, then act. The same goes for a run that a later push will cancel: wait for the new run rather than working under it. See [[verifying-through-ci]] and [[watching-a-run-in-the-background]].
