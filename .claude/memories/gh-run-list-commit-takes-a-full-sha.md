---
name: gh-run-list-commit-takes-a-full-sha
description: "`gh run list --commit` matches only a full 40-character SHA; pass `$(git rev-parse HEAD)`, since a short SHA lists nothing and a loop waiting on it never ends"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-09T08:17:14.871Z
---

# gh run list --commit takes a full SHA

Find a push's run with `gh run list --commit "$(git rev-parse HEAD)"`, never
with the short SHA `git log` or a commit message shows.

**Why:** `--commit` matches the full 40-character SHA only. A short one lists
no run and raises no error, so a watcher that waits for the list to fill
polls until its timeout while the run it was meant to watch has long passed.

**How to apply:** Wherever a command names a commit to `gh`, take the SHA from
`git rev-parse`, not from memory or from text already on screen. Write the
command so it calls `git rev-parse` itself, as
`sha=$(git rev-parse HEAD) && until … --commit "$sha" …`, never with a SHA
typed out, so that no copied SHA can be wrong. The watcher
itself is described in [watching-a-run-in-the-background](watching-a-run-in-the-background.md) and the reading
of its result in [reading-a-ci-run](reading-a-ci-run.md).
