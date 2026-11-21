---
name: git-add-all-or-nothing-pathspecs
description: "git add stages none of its pathspecs when any one matches neither a file on disk nor an index entry, so never name such a path to it."
metadata:
  node_type: memory
  type: project
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:52:19.968Z
---

# git add stages nothing when one pathspec misses

Never name to `git add` a path that is neither on disk nor in the index.

**Why:** `git add` stages none of its pathspecs when any one of them matches nothing. It reports `fatal: pathspec '<path>' did not match any files` and returns non-zero, having staged nothing at all rather than everything but the bad path. A deleted file that is still in the index is a valid pathspec, so `git add old new` after a plain `mv` stages the rename. Once `git mv` or `git rm` has taken the old path out of the index, though, naming it again makes the whole command miss, and a commit made after it carries only what was already staged.

**How to apply:** Stage a removal with `git rm` and the rest with `git add`, naming in each command only paths it can match, then confirm with [reading-the-index-before-committing](reading-the-index-before-committing.md).
