---
name: no-ci-skip-in-commit-messages
description: Never suppress a CI run from a commit message; the workflow on: triggers already decide what runs.
metadata:
  type: feedback
---

# No CI-skip directives in commit messages

Never suppress a CI run from a commit message.

**Why:** The `on:` triggers under `.github/workflows/` already decide which workflows a push needs, and CI is the only review buffer there is — see [verifying-through-ci](verifying-through-ci.md). A skipped run reports neither pass nor fail, so a change that carries one is unverified.

**How to apply:** Write the message without `[skip ci]`, `[ci skip]` or any equivalent, and let the path filters do the selecting. If a workflow is running when it should not, fix its `paths:` rather than the commit message.
