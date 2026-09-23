---
name: waiting-while-a-ci-run-is-in-progress
description: "While any CI run of any workflow is in progress, only wait: no diagnosis, editing or committing until it lands."
metadata: 
  node_type: memory
  type: feedback
---

# Waiting while a CI run is in progress

While any CI run for a pushed commit is in progress -- any workflow under .github/workflows, deltahdl.yml, scripts.yml, documentation.yml or another -- do nothing but wait for it: no probing of the failing file, no edits, no local commits.

**Why:** A run's findings decide the next step, and work done before they land is done on a guess about them.

**How to apply:** After a push, arm the monitor and stop. Read the run when it completes, then act. The same goes for a run that a later push will cancel: wait for the new run rather than working under it. See [[verifying-through-ci]] and [[watching-a-run-in-the-background]].
