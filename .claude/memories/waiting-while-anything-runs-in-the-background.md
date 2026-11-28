---
name: waiting-while-anything-runs-in-the-background
description: "While any command runs in the background, a CI watch or a sweep, wait: start it as a turn's last call and resume the work on its notification; filing an issue and what the user instructs are done at any time, at once."
metadata:
  type: feedback
---

# Waiting while anything runs in the background

While any command runs in the background, whether a CI watch or a sweep of `gh` calls, wait. A background command is the last call of its turn, and the next work starts when its completion notification arrives. Until then there is no reading, searching, diagnosis, planning, editing, staging or committing for the work in hand or any other. Filing an issue is free of the wait: an issue is filed, or an open one rewritten, labelled or closed, as soon as its finding is in hand, during a wait as at any other time, with whatever reading and searching the filing takes.

**Why:** The user wants one thing done at a time, with no switching between pieces of work while something runs. A session that fills a wait drifts: it reads ahead into the next issue, or ticks a case before the test showing it has passed, and the result then lands while its attention is elsewhere. A finding held back for a run to finish only waits to be forgotten, so filing it is never deferred.

**How to apply:**

- Start the background command as the last tool call of the turn, with no other call beside it in that message, then end the turn.
- When a scheduled reminder fires during the wait, acknowledge it in a line and wait on; act on it once the command has finished, unless it asks for an issue to be filed, which is done at once.
- File a finding the moment it is known, without waiting for any run, per [a-finding-joins-the-push-or-is-filed](a-finding-joins-the-push-or-is-filed.md) and [research-lives-in-issues](research-lives-in-issues.md).
- What the user instructs during the wait is the one exception, done in full and at once, per [what-the-user-instructs-is-done](what-the-user-instructs-is-done.md). A question is answered with whatever reading it takes. The wait then goes on.
- A CI run counts while it is in progress, of any workflow. When a later push will cancel it, wait for the new run rather than working under the old one.
- Never leave two commands running side by side to fill the time; when a step needs two results, put both in one background command.
- See [long-running-commands-in-the-background](long-running-commands-in-the-background.md) and [verifying-through-ci](verifying-through-ci.md).
