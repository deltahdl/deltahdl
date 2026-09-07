---
name: closing-keyword-form
description: Write a close as Closes #N and a mention as Refs #N or See #N; nothing enforces it.
metadata:
  type: feedback
---

# The form of an issue reference

Write a close as `Closes #N`, and a mention as `Refs #N` or `See #N`.

**Why:** GitHub honours nine closing keywords and any of them works, so nothing enforces the choice and a commit written with a different one closes its issue exactly the same way. This repository writes `Closes`: 3343 commits open a line with `Closes #N` against 11 with `Fixes #N`. Where a commit only mentions an issue, `Refs` and `See` are the words the history uses, and a bare `#N` with no keyword before it does the same job. What the shared form buys is a log that can be read for finishing commits by searching a single word.

**How to apply:** Pick the word by whether the commit finishes the issue, per [issue-closing-keywords-fire-on-push](issue-closing-keywords-fire-on-push.md), and write one line per issue, per [one-closing-keyword-per-issue](one-closing-keyword-per-issue.md).
