---
name: one-commit-is-a-whole-body-of-work
description: "Each pushed commit holds a whole body of work (an issue solved end to end, or a request carried out in full), never one step of it."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0eac2fc8-aa5f-4f95-9fa7-69e4f3f0a42a
  modified: 2026-09-23T01:59:30.359Z
---

# One commit is a whole body of work

A push carries one commit, and that commit holds a whole body of work: an issue solved end to end, or a request of the user's carried out in full. A step of that work is not pushed on its own.

**Why:** On 2026-09-22 the user said the commits were so small that too much time went to waiting on CI for each one.

**How to apply:** Keep the work uncommitted until the body is complete, then commit once and push. See [[pushing-to-main]].
