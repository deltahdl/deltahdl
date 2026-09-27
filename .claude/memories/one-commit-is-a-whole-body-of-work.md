---
name: one-commit-is-a-whole-body-of-work
description: "Each pushed commit holds a whole body of work, never one step of it: a matter solved end to end, or a batch of issues of one matter solved in full."
metadata:
  node_type: memory
  type: feedback
---

# One commit is a whole body of work

A push carries one commit, and that commit holds a whole body of work. That body is either a matter solved end to end or carried out in full, or a batch of issues of one matter, every one of them solved ([[grouping-issues-into-a-push]]). A step of that work is never pushed on its own, and neither is part of a batch.

**Why:** Every push waits on CI. Work pushed a step at a time, or an issue at a time, spends most of its time waiting.

**How to apply:** Keep the work uncommitted until the body is complete, then commit once and push. For a batch, that means after its last issue. See [[pushing-to-main]].
