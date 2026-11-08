---
name: cache-budget-is-two-generations
description: "The repository's 10 GB Actions cache has to hold two generations of every cached job, so a new cached job is budgeted at twice what one build of it stores."
metadata:
  node_type: memory
  type: project
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:46.523Z
---

# The cache budget is two generations

Every ccache and ctcache key in `.github/workflows/deltahdl.yml` ends in the commit's SHA, so each run writes a new generation. The prune job removes a superseded generation only after the new one is written, so two generations of every cached job sit in the cache at once.

**Why:** GitHub gives the repository 10 GB of cache for all jobs together, and reclaims an overage by evicting whatever was used least recently. An overage doesn't cost the job that caused it. It costs some other job its whole cache, and that job then compiles from nothing.

**How to apply:** Before adding a cached job, or letting one store more, check that twice the new total of what one run of every cached job stores still fits under 10 GB. Keys that name what they hold rather than a commit (`sv-tests-*`, `pmd-*`, `pip-*`) never go stale, and the prune leaves them alone.
