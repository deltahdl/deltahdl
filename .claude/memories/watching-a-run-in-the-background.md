---
name: watching-a-run-in-the-background
description: "Watch a CI run with a background shell or a Monitor, never a foreground `gh run watch` that blocks the turn."
metadata:
  node_type: memory
  type: feedback
  originSessionId: bdfa5c79-c458-40ad-ac44-7216148a3e6b
  modified: 2026-09-28T01:32:27.071Z
---

# Watching a run in the background

Wait for a CI run with `run_in_background: true` on the Bash call, or with the Monitor tool, and let the notification bring the result back; never block the turn on a foreground `gh run watch`.

**Why:** A foreground watch holds the whole session for the length of the run, and nothing else, a reminder included, can arrive while it does.

**How to apply:** After the push in [reading-a-ci-run](reading-a-ci-run.md), start `gh run watch <id> --exit-status` as a background Bash command and let its completion notification bring the result, then read the run with `gh run view --log-failed` as usual. Find the run's id with `gh run list --commit "$(git rev-parse HEAD)"`: `--commit` matches only a full SHA, so a short one lists nothing, and a loop waiting for it to list a run never ends. The waiting rule of the autopilot's :07 reminder still holds: do nothing else while the run is going.

Any foreground wait counts, not only `gh run watch`: an `until ... ; do sleep 60; done` poll, or a loop reading a background task's output file until it fills, blocks the session just the same, and the user cannot type while it runs. Once the background watcher is started, end the turn and let its notification resume the work; never add a foreground wait on top of it.
