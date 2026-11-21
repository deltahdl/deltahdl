---
name: one-commit-per-push
description: "Each push carries exactly one commit; a second commit is made only after the first is pushed, so local main is never more than one commit ahead of origin."
metadata:
  node_type: memory
  type: feedback
  originSessionId: a2550b1a-b158-4abd-afb7-e28ebe990d2f
  modified: 2026-11-21T02:19:31.733Z
---

# One commit per push

Every push carries exactly one commit. Local `main` is never more than one commit ahead of `origin/main`: once a commit is made, it is checked with the `pre-push-checks` skill and pushed before the next commit is made. Work that would go into a second commit before the first is pushed either joins the first, by amending it while it is still unpushed, or waits until the first is pushed.

**Why:** CI checks a push as one run against its head. With several commits in a push, a red run cannot be pinned on one of them, and a red-run fix pushed alongside other work stops being a push of its own ([fixing-a-red-run](fixing-a-red-run.md)).

**How to apply:**

- Before `git commit`, check `git rev-list --count origin/main..HEAD` is 0; if a commit is still unpushed, push it first ([draining-the-push-queue-first](draining-the-push-queue-first.md)) or amend it instead of committing anew.
- An issue closed in a commit still closes in that one commit ([a-commit-closes-an-issue](a-commit-closes-an-issue.md)); several issues finished together go in one commit, not in several commits pushed together.
- A change the user asks for mid-way, such as a memory edit, waits for the commit in hand to be pushed, then gets its own commit and push.
