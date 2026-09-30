---
name: gh-run-list-commit-takes-a-full-sha
description: "`gh run list --commit` matches only a full 40-character SHA; pass `$(git rev-parse HEAD)`, since a short SHA lists nothing and a loop waiting on it never ends"
metadata:
  type: feedback
---

# gh run list --commit takes a full SHA

Find a push's run with `gh run list --commit "$(git rev-parse HEAD)"`, never
with the short SHA `git log` or a commit message shows.

**Why:** `--commit` matches the full 40-character SHA only. A short one lists
no run and raises no error, so a watcher that waits for the list to fill
polls until its timeout while the run it was meant to watch has long passed.

**How to apply:** Wherever a command names a commit to `gh`, take the SHA from
`git rev-parse`, not from memory or from text already on screen. The watcher
itself is described in [[watching-a-run-in-the-background]] and the reading
of its result in [[reading-a-ci-run]].
