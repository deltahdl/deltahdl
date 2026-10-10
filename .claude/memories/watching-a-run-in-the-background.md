---
name: watching-a-run-in-the-background
description: "Watch a CI run with a background shell or a Monitor, never a foreground `gh run watch` that blocks the turn."
metadata:
  node_type: memory
  type: feedback
  originSessionId: bdfa5c79-c458-40ad-ac44-7216148a3e6b
  modified: 2026-10-10T07:29:29.559Z
---

# Watching a run in the background

Wait for a CI run with `run_in_background: true` on the Bash call, or with the Monitor tool, and let the notification bring the result back; never block the turn on a foreground `gh run watch`.

**Why:** A foreground watch holds the whole session for the length of the run, and nothing else, a reminder included, can arrive while it does.

**How to apply:** After the push in [reading-a-ci-run](reading-a-ci-run.md), start `gh run watch <id> --exit-status` as a background Bash command and let its completion notification bring the result, then read the run with `gh run view --log-failed` as usual. Find the run's id as [[gh-run-list-commit-takes-a-full-sha]] says. The waiting rule of the autopilot's :07 reminder still holds: do nothing else while the run is going.

Any foreground wait counts, not only `gh run watch`: an `until ... ; do sleep 60; done` poll, or a loop reading a background task's output file until it fills, blocks the session just the same, and the user cannot type while it runs. Once the background watcher is started, end the turn and let its notification resume the work; never add a foreground wait on top of it.

Pass `--interval 60` to `gh run watch`. Its default polls every 3 seconds, and over a run of most of an hour that tripped GitHub's rate limit: the watch and every `gh` call after it came back HTTP 403 while `gh api rate_limit` still showed every bucket full, the mark of the secondary limit, which clears only after minutes of quiet. When it trips, wait in a background `sleep` before the next `gh` call rather than retrying.

The same holds for any long command, not only a CI watch: see [long-running-commands-in-the-background](long-running-commands-in-the-background.md).
