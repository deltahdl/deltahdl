---
name: git-add-all-swept-scratch
description: One `git add -A` put about 112,000 lines of untracked scratch into commit 9df98e152.
metadata:
  type: project
---

# The `git add -A` that swept the scratch directories in

One `git add -A` swept about 112,000 lines of untracked scratch directories into commit `9df98e152`, which the user caught. Recovering meant `git rm -r --cached`, a `.gitignore` entry, an amend, and a force-push with lease to scrub it from history.

Supports [staging-explicit-paths](../rules/staging-explicit-paths.md).
