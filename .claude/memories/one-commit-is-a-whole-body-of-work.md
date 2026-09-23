---
name: one-commit-is-a-whole-body-of-work
description: "Each pushed commit holds a whole body of work (an issue solved end to end, or a request carried out in full), never one step of it."
metadata:
  node_type: memory
  type: feedback
---

# One commit is a whole body of work

A push carries one commit, and that commit holds a whole body of work: an issue solved end to end, or a request of the user's carried out in full. A step of that work is not pushed on its own.

**Why:** Every push waits on CI, so work pushed a step at a time spends most of its time waiting.

**How to apply:** Keep the work uncommitted until the body is complete, then commit once and push. See [[pushing-to-main]].
