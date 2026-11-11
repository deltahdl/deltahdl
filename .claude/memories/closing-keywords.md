---
name: closing-keywords
description: "Nine keywords close an issue from anywhere in a commit message pushed to main, brackets included; write `Closes #N` once per finished issue, each on its own line, and `Refs #N` or `See #N` for a mention."
metadata:
  node_type: memory
  type: project
  originSessionId: b425c181-0dc9-4105-9628-ad8462acdd57
  modified: 2026-11-11T01:25:52.991Z
---

# Closing keywords

GitHub closes any issue referenced as `fix`, `fixes`, `fixed`, `close`, `closes`, `closed`, `resolve`, `resolves` or `resolved` followed by `#N`, anywhere in a commit message pushed to the default branch. Brackets do not disable it: `Fix the gate (#N)` is read as `fix #N` and closes the issue. A keyword binds to exactly one number, so `Closes #N, #M, #P` closes the first and leaves the rest open while reading as though it closed all three.

This repository writes `Closes #N` for an issue the commit finishes, and `Refs #N` or `See #N` for one it only mentions; a bare `#N` mentions too.

**Why:** Work goes straight to `main`, per [pushing-to-main](pushing-to-main.md), so there is no pull-request stage at which a premature close could be caught. Any of the nine words works, so nothing enforces the choice; writing `Closes` alone keeps the log searchable for finishing commits by one word.

**How to apply:**

- Write a closing keyword beside each issue the commit finishes and beside no other; every commit finishes at least one, per [a-commit-closes-an-issue](a-commit-closes-an-issue.md).
- Where the message mentions an issue it does not finish, use `Refs` or `See`, or rephrase a title that would read as a keyword.
- Give each finished issue a line of its own:

```text
Closes #N
Closes #M
Closes #P
```

- After the push, read the states back, per [confirming-a-push-closed-its-issues](confirming-a-push-closed-its-issues.md), rather than trusting the shape of the message.
