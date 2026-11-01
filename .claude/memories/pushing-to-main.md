---
name: pushing-to-main
description: Commit straight to main; there is no pull-request cycle in this repository.
metadata:
  node_type: memory
  type: feedback
  originSessionId: 03cfcaf6-69fa-40b2-b2b5-b6a99bf34be9
  modified: 2026-09-30T22:51:29.565Z
---

# Pushing to main

Commit directly to `main`. Do not frame work as pull requests, do not suggest opening one, and do not structure advice around review cycles.

A requested change is finished when it is committed and pushed, so commit and push it without asking whether to: asking only holds back work the user has already asked for.

**Why:** This repository has no pull-request cycle: work is pushed to `main`, and `git log --merges` on `main` is empty.

**How to apply:** Use commits as the unit when breaking work down, and think in commit ordering rather than branch-and-merge. Two consequences follow: a closing keyword in a commit title fires the moment it is pushed, and CI is the only review buffer there is. See [issue-closing-keywords-fire-on-push](issue-closing-keywords-fire-on-push.md) and [verifying-through-ci](verifying-through-ci.md).
