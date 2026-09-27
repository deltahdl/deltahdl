---
name: draining-the-push-queue-first
description: "While commits sit committed locally but unpushed, take no new issue: squash the queue, in its own order, into as few commits as possible and push one per clean run until it is empty."
metadata:
  node_type: memory
  type: feedback
---

# Draining the push queue first

While any commit sits on local `main` unpushed, take no new issue. Drain the queue in as few pushes as it allows without conflicts, and pick up the next issue only once `git rev-list origin/main..HEAD` is empty.

**Why:** Every queued commit is work CI has not yet verified. Solving new issues on top of the queue grows that backlog faster than the pushes drain it, and it lets the queued commits go stale against the tree. When a run goes red, the fix has to be rebased under the whole stack above it. The user asked for the queue to be merged into as few pushes as possible, as long as the merging creates no conflicts, with each push carrying a single commit.

**How to apply:** Squash the queue in its own order: a batch is a run of consecutive queued commits, never a selection of commits that touch disjoint files. Two commits that share no file can still depend on each other, as when one calls a function another exports from a different file, so a batch lifted out of order can fail to build even though every rebase applied cleanly. With the order kept, the whole queue goes as one commit whose subject joins the leading clause of every commit it holds and whose body keeps each commit's message, with one `Closes #N` line per issue. Push it and wait for its run. A red run is diagnosed from its log and its defects fixed in the next push. See [[one-commit-is-a-whole-body-of-work]], [[waiting-while-a-ci-run-is-in-progress]] and [[fixing-a-red-run]].
