# The form of an issue reference

Write a close as `Closes #N`, and a mention as `Refs #N` or `See #N`.

GitHub honours nine closing keywords, and any of them works. This repository writes `Closes`: 3343 commits open a line with `Closes #N` against 11 with `Fixes #N`. Where a commit only mentions an issue, `Refs` and `See` are the words the history uses, and a bare `#N` with no keyword before it does the same job.

Nothing enforces the choice, and a commit written with a different one of the nine closes its issue exactly the same way. What the shared form buys is a log that can be read for finishing commits by searching a single word.

Related: [issue-closing-keywords](../rules/issue-closing-keywords.md) for what the keyword does, and when to reserve it.
