---
name: fetching-a-failed-job-log
description: "When gh run view --log-failed breaks off or returns nothing, fetch each failed job's log through gh api with --allow-escape-sequences"
metadata:
  node_type: memory
  type: reference
  originSessionId: e369d221-53b5-462f-a852-c227f5a063c9
  modified: 2026-10-10T14:07:37.084Z
---

# Fetching a failed job's log

`gh run view <id> --log-failed` can end in a stream CANCEL error, and `gh run view --job <id> --log-failed` can write nothing. When that happens, list the failed jobs with `gh run view <id> --json jobs --jq '.jobs[]|select(.conclusion=="failure")|.databaseId'`. Then fetch each one with `gh api --allow-escape-sequences repos/deltahdl/deltahdl/actions/jobs/<job id>/logs`, piped through `sed 's/\x1b\[[0-9;]*m//g'`. Without the flag, `gh api` refuses the body: the log holds terminal colour codes.

Pairs with [reading-a-ci-run](reading-a-ci-run.md) and [watching-a-run-in-the-background](watching-a-run-in-the-background.md).
