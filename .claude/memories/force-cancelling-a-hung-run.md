---
name: force-cancelling-a-hung-run
description: "A job hung inside a step ignores a plain gh run cancel and cannot be deleted while in progress; gh run cancel --force ends it, then gh run rerun --failed"
metadata:
  node_type: memory
  type: reference
  originSessionId: d9c89566-9e43-4ded-9871-cf27b7225b5b
  modified: 2026-10-18T05:05:58.366Z
---

# Force-cancelling a hung run

A CI job stuck inside a step (a stalled package install, say) ignores a plain `gh run cancel`: the request is accepted and the run stays `in_progress`. `gh run delete` refuses an unfinished run with HTTP 403. `gh run cancel <id> --force` ends it, within a few minutes; then `gh run rerun <id> --failed` re-runs only the cancelled job and keeps every job that already passed. The workflow sets no `timeout-minutes`, so left alone a hung job holds the run for GitHub's 360-minute default.

**How to apply:** when one job of a run sits on a step far past its usual duration (compare its earlier runs with `gh run view <id> --json jobs`), go straight to `--force`, wait for the run to complete, rerun `--failed`, and watch the new attempt. See [[watching-a-run-in-the-background]].
