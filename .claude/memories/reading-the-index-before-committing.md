---
name: reading-the-index-before-committing
description: Read the index back with git status --porcelain after staging and before committing.
metadata:
  type: feedback
---

# Reading the index back before committing

Run `git status --porcelain` after staging and before committing, and compare what it lists against what the change touched.

**Why:** A failed staging command returns non-zero, and that decides nothing when `git add` and `git commit` are separate lines rather than one `&&` chain, because nothing reads the exit status. Reading the index is what makes the failure visible whatever caused it, and it costs one command.

**How to apply:** One `git status --porcelain` between staging and committing, every time. It catches the miss in [git-add-all-or-nothing-pathspecs](git-add-all-or-nothing-pathspecs.md) and the sweep in [git-add-explicit-paths](git-add-explicit-paths.md) alike.
