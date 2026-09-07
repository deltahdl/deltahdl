---
name: commit-subject-length
description: Write the commit subject at the length that states the change, and leave the body unwrapped.
metadata:
  type: feedback
---

# The length of a commit subject

Write the subject at the length that states the change, and leave the body unwrapped.

**Why:** A subject truncated to a conventional width states less than the change it names, and a body hard-wrapped at a column re-wraps badly wherever it is read. The general form of this is [prose-length-over-column-fitting](prose-length-over-column-fitting.md).

**How to apply:** Say the whole change in the subject and stop there; do not pad it to a width and do not cut it to one. Put the closing keywords on their own lines below, per [one-closing-keyword-per-issue](one-closing-keyword-per-issue.md).
