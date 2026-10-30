---
name: a-push-that-starts-no-run
description: "A push GitHub never hands to Actions leaves its commit with no check suite and no run; `gh workflow run deltahdl.yml --ref main` starts the run for the head commit, as the workflow's workflow_dispatch trigger allows"
metadata:
  node_type: memory
  type: reference
  originSessionId: bb5048d0-508d-423a-95b6-240378a5c78f
  modified: 2026-10-21T15:47:31.538Z
---

# A push that starts no run

GitHub can accept a push to main and never start a run for it: the commit
then lists no check suite at all
(`gh api repos/{owner}/{repo}/commits/<sha>/check-suites --jq .total_count`
answers 0), and `gh run list --commit <sha>` stays empty however long it is
waited on. A path filter is not the cause when an earlier push touching the
same paths started one.

**Why:** The workflow's own trigger list holds `workflow_dispatch` beside
`push`, so a run can be started by hand on main, and it runs the commit at
main's head with the same jobs a push would have started. Waiting longer
gets nothing, and pushing again to provoke a run would need an empty commit
that changes nothing.

**How to apply:** When a watcher finds no run for a pushed commit after
several minutes, check the commit's check suites; at 0, run
`gh workflow run deltahdl.yml --ref main`, confirm with
`gh run list --workflow deltahdl.yml --limit 1` that the queued run names
the pushed SHA, and watch that run id in the background as
[[watching-a-run-in-the-background]] has it. The dispatched run's event is
`workflow_dispatch`, so a watcher keyed on
[[gh-run-list-commit-takes-a-full-sha]] still finds it by its SHA.
