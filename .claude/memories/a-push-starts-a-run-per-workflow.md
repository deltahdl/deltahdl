---
name: a-push-starts-a-run-per-workflow
description: "A push can start a run of more than one workflow, `deltahdl` and `scripts` among them; `gh run list --commit <sha> --limit 1` returns only one, so watch every run the commit started or filter with `--workflow deltahdl`"
metadata:
  node_type: memory
  type: feedback
  originSessionId: fb164f96-9266-4e2a-88a8-70f275fdbb36
  modified: 2026-10-21T03:34:54.604Z
---

# A push starts a run per workflow

A push to main starts a run of every workflow whose path filter it matches,
so one commit can have a `deltahdl` run and a `scripts` run side by side.
Watch every run `gh run list --commit <sha>` lists, or name the one that
holds the verdict with `--workflow deltahdl`.

**Why:** `gh run list --commit <sha> --limit 1` returns only one of the
commit's runs, and it may be the short `scripts` one. Read alone, its green
conclusion passes for the push's verdict while the `deltahdl` run is still
going.

**How to apply:** In a watcher, loop over every run id the commit lists
rather than taking the first. The SHA it names is a full one, as
[[gh-run-list-commit-takes-a-full-sha]] has it, and the watcher runs in the
background, as [[watching-a-run-in-the-background]] has it.
