---
name: git-add-all-or-nothing-pathspecs
description: git add stages none of its pathspecs when any one matches nothing, so never name a removed path to it.
metadata:
  type: project
---

# git add stages nothing when one pathspec misses

Name a removed path to `git rm` and an added or modified path to `git add`, and never name both kinds to one command.

**Why:** `git add` stages none of its pathspecs when any one of them matches nothing on disk. It reports `fatal: pathspec '<path>' did not match any files` and returns non-zero, having staged nothing at all rather than everything but the bad path. A rename is what produces such a list, because the old path is gone from disk while the new one is not yet tracked, so a session listing every path a rename touched hits this on the first try. Commit `c45398c25` is what that costs: a bare 997-line deletion landed on `main` with neither replacement file staged, and `6e63b7c56` added what the split was meant to carry.

**How to apply:** Split the staging into a `git rm` for what is gone and a `git add` for what is there, then confirm with [reading-the-index-before-committing](reading-the-index-before-committing.md).
