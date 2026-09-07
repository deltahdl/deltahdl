---
name: git-add-explicit-paths
description: Stage each file by explicit path; never git add -A or git add . in this repository.
metadata:
  type: feedback
---

# Staging explicit paths

Never use `git add -A` or `git add .`. Stage each file by its path.

**Why:** `.gitignore` excludes `.claude/scheduled_tasks.lock` and not the rest of `.claude/`, which carries the session notes and `.claude/skills/`, so a `git add -A` there stages a session's lock file alongside them. Other untracked scratch appears from time to time as well, so explicit staging is the rule regardless.

**How to apply:** Name every path. Then read the index back before committing — see [reading-the-index-before-committing](reading-the-index-before-committing.md) — and keep removals off the `git add` line, per [git-add-all-or-nothing-pathspecs](git-add-all-or-nothing-pathspecs.md).
