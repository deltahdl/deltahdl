---
name: commit-subject-length
description: Keep the commit subject short, about 72 characters, naming the change; put the detail in a body left unwrapped.
metadata:
  type: feedback
---

# The length of a commit subject

Keep the subject short, about 72 characters, naming what the change does, and put the detail in the body, left unwrapped.

**Why:** GitHub, `git log --oneline` and most other views cut a subject at about that width, so a paragraph-long subject is truncated exactly where it is read most, while the body has room for the whole change. A body hard-wrapped at a column re-wraps badly wherever it is read ([prose-length-over-column-fitting](prose-length-over-column-fitting.md)).

**How to apply:** Write a subject naming the change, then a blank line and a body saying what changed and why. Put the closing keywords on their own lines below, per [one-closing-keyword-per-issue](one-closing-keyword-per-issue.md).
