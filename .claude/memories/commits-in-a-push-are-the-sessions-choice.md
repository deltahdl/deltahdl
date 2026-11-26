---
name: commits-in-a-push-are-the-sessions-choice
description: "How many commits a push carries, one or several, and when it goes are both the session's choice; every workflow's run page lists a push's commits through its summarize-commits job."
metadata:
  node_type: memory
  type: feedback
  originSessionId: be53c13f-03bb-4ddf-b834-c4e0b8cde655
  modified: 2026-11-26T15:21:39.051Z
---

# Commits in a push are the session's choice

A push carries one commit or several, as the session judges best for the work, and the session chooses when to push. Nothing asks for a single commit or for several: one commit holding a whole change is as right as several commits that each take a step of it.

**Why:** The user leaves both how the work is cut into commits and when it is pushed to the session's judgment. A run page names only the push's head commit, so every workflow carries a `summarize-commits` job, from the composite action `.github/actions/summarize-commits`, which lists every commit of the push on that run's summary page; the user reads the commits there.

**How to apply:**

- Each commit carries its own tests with its code ([test-driven-development](test-driven-development.md)). A commit may close an issue or only move one forward; the push as a whole closes at least one ([a-push-closes-an-issue](a-push-closes-an-issue.md)).
- A push waits for no run to be in progress ([reading-a-ci-run](reading-a-ci-run.md)), and a red-run fix goes in a push of its own ([fixing-a-red-run](fixing-a-red-run.md)).
- A red run is read against the push as a whole; the log names the failing check, and the commit that touched it is found from the push's list.
- A new workflow gets the `summarize-commits` job, the action in its `paths` filter and in its `assert-no-comments` trees ([workflow-paths-name-the-programs-its-jobs-run](workflow-paths-name-the-programs-its-jobs-run.md)).
