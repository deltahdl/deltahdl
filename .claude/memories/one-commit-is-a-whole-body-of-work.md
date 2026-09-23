---
name: one-commit-is-a-whole-body-of-work
description: "Each pushed commit holds a whole body of work (an issue end to end, a request in full), never one step of it, because every push costs a full deltahdl.yml run."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0eac2fc8-aa5f-4f95-9fa7-69e4f3f0a42a
  modified: 2026-09-23T01:58:12.748Z
---

# One commit is a whole body of work

A push carries one commit, and that commit holds a whole body of work: an issue solved end to end, or a request of the user's carried out in full, together with its unit and integration cases, the tooling and workflow changes it needs, and the fix of anything found along the way. A helper, a test, a rename, a library move or a lint fix is a step of such a body and is not pushed alone. The fix of a red run joins the body in hand rather than going out by itself.

**Why:** On 2026-09-22 the user said the commits were "so small that we are spending too much time waiting for deltahdl.yml to run for every tiny thing you push". That day had gone out as a string of one-step pushes (a shared-helper move, then the runner, then a lint fix, then a table move), each waiting on a full run.

**How to apply:** Keep the work uncommitted until the body is complete, then stage it all, commit once and push. Plan the task list with one commit, push and read-the-run triple per body, not per step. This sits alongside [[pushing-to-main]] and [[waiting-while-a-ci-run-is-in-progress]]: fewer pushes also means fewer waits.
