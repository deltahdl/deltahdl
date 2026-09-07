---
name: one-closing-keyword-per-issue
description: A closing keyword binds to exactly one #N, so repeat it on its own line for each issue a commit finishes.
metadata:
  type: project
---

# One closing keyword per issue

Repeat the keyword on its own line for each issue a commit finishes.

**Why:** A keyword binds to exactly one number, so `Closes #N, #M, #P` closes the first and leaves the rest open while reading as though it closed all three.

**How to apply:** Write them out:

```text
Closes #N
Closes #M
Closes #P
```

That form has closed ten issues in a single commit here. After a multi-issue close, read the states back with `gh issue view <N> --json state` rather than trusting the shape of the message.
