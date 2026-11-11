---
name: waiting-while-anything-runs-in-the-background
description: "While any command runs in the background, a CI watch, a build, a test run, the pre-push check or a sweep, do nothing but wait: start it as a turn's last call and act again only on its notification."
metadata:
  type: feedback
---

# Waiting while anything runs in the background

While any command runs in the background, whether a CI watch, a build, a test run, the `pre-push-checks` skill, a probe or a sweep of `gh` calls, do nothing but wait. A background command is the last call of its turn, and the next work starts when its completion notification arrives. Until then there is no reading, searching, diagnosis, planning, editing, staging, committing or issue writing, for the issue in hand or any other.

**Why:** The user wants one thing done at a time, with no switching between pieces of work while something runs. A session that fills a wait drifts: it reads ahead into the next issue, or ticks a case before the test showing it has passed, and the result then lands while its attention is elsewhere. Locally there is a second reason: `check.sh` and a build read the working tree until they finish, so an edit made while they run is checked in place of the commit. The local waits are short besides, under about a minute for `check.sh` once `build-check/` is built, so filling them gains nothing.

**How to apply:**

- Start the background command as the last tool call of the turn, with no other call beside it in that message, then end the turn.
- When a scheduled reminder fires during the wait, acknowledge it in a line and wait on; act on it once the command has finished.
- When the user writes during the wait, answer from what is already known, and do the work their message asks for once the command has finished, unless they say to do it now.
- A CI run counts while it is in progress, of any workflow. When a later push will cancel it, wait for the new run rather than working under the old one.
- Never leave two commands running side by side to fill the time; when a step needs two results, put both in one background command.
- See [long-running-commands-in-the-background](long-running-commands-in-the-background.md) and [verifying-through-ci](verifying-through-ci.md).
