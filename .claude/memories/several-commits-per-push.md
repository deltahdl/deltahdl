---
name: several-commits-per-push
description: "A push may carry several commits, each one a whole step of the work; every workflow's run page lists them all through its summarize-commits job."
metadata:
  node_type: memory
  type: feedback
  originSessionId: be53c13f-03bb-4ddf-b834-c4e0b8cde655
  modified: 2026-11-26T14:58:39.085Z
---

# Several commits per push

A push may carry several commits. Work is broken into small commits, each a whole step that stands on its own, and they are pushed together once the work is done.

**Why:** Small commits keep each change readable and revertable on its own. A run page names only the push's head commit, so every workflow carries a `summarize-commits` job, from the composite action `.github/actions/summarize-commits`, which lists every commit of the push on that run's summary page; the user reads the commits there.

**How to apply:**

- Each commit carries its own tests with its code ([test-driven-development](test-driven-development.md)) and closes its issues ([a-commit-closes-an-issue](a-commit-closes-an-issue.md)).
- A push still waits for no run to be in progress ([reading-a-ci-run](reading-a-ci-run.md)), and a red-run fix still goes in a push of its own ([fixing-a-red-run](fixing-a-red-run.md)).
- A red run is read against the push as a whole; the log names the failing check, and the commit that touched it is found from the push's list.
- A new workflow gets the `summarize-commits` job, the action in its `paths` filter and in its `assert-no-comments` trees ([workflow-paths-name-the-programs-its-jobs-run](workflow-paths-name-the-programs-its-jobs-run.md)).
