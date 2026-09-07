---
name: pushing-to-main
description: Commit straight to main; there is no pull-request cycle in this repository.
metadata:
  type: feedback
---

# Pushing to main

Commit directly to `main`. Do not frame work as pull requests, do not suggest opening one, and do not structure advice around review cycles.

**Why:** The user stated it plainly — "we push to main. we dont do PRs" — and `git log --merges` on `main` is empty.

**How to apply:** Use commits as the unit when breaking work down, and think in commit ordering rather than branch-and-merge. Two consequences follow: a closing keyword in a commit title fires the moment it is pushed, and CI is the only review buffer there is. See [issue-closing-keywords-fire-on-push](issue-closing-keywords-fire-on-push.md) and [verifying-through-ci](verifying-through-ci.md).
