---
name: watching-a-run-in-the-background
description: "Watch a CI run with a background shell or a Monitor, never a foreground `gh run watch` that blocks the turn."
metadata: 
  node_type: memory
  type: feedback
---

# Watching a run in the background

Wait for a CI run with `run_in_background: true` on the Bash call, or with the Monitor tool, and let the notification bring the result back; never block the turn on a foreground `gh run watch`.

**Why:** A foreground watch holds the whole session for the length of the run, and nothing else, a reminder included, can arrive while it does.

**How to apply:** After the push in [reading-a-ci-run](reading-a-ci-run.md), start `gh run watch <id> --exit-status` as a background Bash command and wait for its completion notification, then read the run with `gh run view --log-failed` as usual. The waiting rule of the autopilot's :07 reminder still holds: do nothing else while the run is going.
