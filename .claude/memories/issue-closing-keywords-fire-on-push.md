---
name: issue-closing-keywords-fire-on-push
description: Nine keywords close an issue from any part of a commit message pushed to main, and brackets do not disable them.
metadata:
  type: project
---

# Issue-closing keywords fire on push

GitHub closes any issue referenced as `fix`, `fixes`, `fixed`, `close`, `closes`, `closed`, `resolve`, `resolves` or `resolved` followed by `#N`, anywhere in a commit message pushed to the default branch. Brackets do not disable it: `Fix the gate (#N)` is read as `fix #N` and closes the issue.

**Why:** Work here goes straight to `main` — see [pushing-to-main](pushing-to-main.md) — so there is no pull-request stage at which a premature close could be caught.

**How to apply:** Write a closing keyword beside each issue the commit finishes and beside no other; every commit finishes at least one, per [a-commit-closes-an-issue](a-commit-closes-an-issue.md). Where a commit also mentions an issue it does not finish, use a non-closing word for it or rephrase the title; [closing-keyword-form](closing-keyword-form.md) gives the words this repository writes for each case.
