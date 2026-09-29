---
name: fixing-a-red-run
description: "When the run a session's push starts goes red, that session fixes it, whether the push broke something or inherited the break."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 4b8a993c-534c-43f4-83e5-0185606256e0
  modified: 2026-09-29T01:04:16.910Z
---

# Fixing a red run after a push

When the CI run a push starts goes red, the session that pushed fixes it, whether the push caused the failure or inherited it from an earlier commit. What sets the rule off is a push's own run going red, not a red run the session merely comes across.

**Why:** A change is unverified until the jobs that build and test have actually run, and a conclusion of `failure` reads the same whether the change broke something or inherited a break. A skipped job reports neither pass nor fail. So an inherited failure hides the change's own result for as long as it stands, and the session that pushed is the one whose change is left unverified.

**How to apply:** Once the push's run has completed, `gh run view --log-failed` tells a break the change caused from one it inherited ([[reading-a-ci-run]]). Fix both kinds — see [solving-what-a-session-finds](solving-what-a-session-finds.md). A failing `sv-tests-coverage` job in `.github/workflows/deltahdl.yml` is no exception. The fix goes in a push of its own, before the next batch of issues ([[grouping-issues-into-a-push]]). Pushed together, a second red run could not say whether the fix or the batch broke it.
