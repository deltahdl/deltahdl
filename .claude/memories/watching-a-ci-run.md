---
name: watching-a-ci-run
description: "Watch a CI run with `gh run watch <id> --interval 60 --exit-status` in the background or with the Monitor tool; the default 3-second poll trips GitHub's secondary rate limit over a long run."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:52:59.825Z
---

# Watching a CI run

Watch a run with `gh run watch <id> --interval 60 --exit-status`, started as a background Bash command, or with the Monitor tool, and let the notification bring the result.

**Why:** `gh run watch` in the foreground holds the whole session for the length of the run ([long-running-commands-in-the-background](long-running-commands-in-the-background.md)). Its default interval polls every 3 seconds, and over a run of most of an hour that trips GitHub's secondary rate limit: every `gh` call then answers HTTP 403 while `gh api rate_limit` still shows every bucket full, and it clears only after minutes of quiet.

**How to apply:** Find the run's id with the full SHA ([gh-run-list-commit-takes-a-full-sha](gh-run-list-commit-takes-a-full-sha.md)) and watch every run the commit started ([a-push-starts-a-run-per-workflow](a-push-starts-a-run-per-workflow.md)). Always pass `--interval 60`. When the rate limit trips, wait in a background `sleep` before the next `gh` call rather than retrying. Once the run completes, read it as [reading-a-ci-run](reading-a-ci-run.md) says.
