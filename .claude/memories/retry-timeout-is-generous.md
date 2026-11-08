---
name: retry-timeout-is-generous
description: "The retry helper in the install-llvm action bounds each attempt by RETRY_TIMEOUT, which is set well above how long the command takes when it makes progress."
metadata:
  node_type: memory
  type: project
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:42.419Z
---

# RETRY_TIMEOUT is set generously

The `retry` function in `.github/actions/install-llvm/action.yml` runs each attempt under `timeout -k 30 "${RETRY_TIMEOUT}"`. The default is 300 seconds, and the `apt-get install` raises it to 900 before calling `retry`.

**Why:** The bound exists for an attempt that makes no progress at all, a mirror that accepted the connection and then went quiet. A bound tight enough to cut off a slow mirror that is still sending fails an attempt that would have finished, and after five of them a green run turns red.

**How to apply:** When a command run through `retry` legitimately takes longer than 300 seconds, set `RETRY_TIMEOUT` before its call, with room to spare over its slowest measured run. Never tighten it to make a stall fail sooner. The `curl` and `git` bounds inside an attempt (`--connect-timeout`, `--max-time`, `Acquire::*::Timeout`, `GIT_HTTP_LOW_SPEED_*`) fail the request, and `timeout` fails the attempt.
