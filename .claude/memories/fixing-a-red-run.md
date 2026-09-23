---
name: fixing-a-red-run
description: Fix a red run in the session that finds it, whoever caused it; a pre-existing failure is a task, not a disposition.
metadata:
  type: feedback
---

# Fixing a red run in the session that finds it

Fix a red run in the session that finds it, whoever caused it.

**Why:** A change is unverified until the jobs that build and test have actually run, and a conclusion of `failure` reads the same whether the change broke something or inherited a break. A skipped job reports neither pass nor fail. So an inherited failure hides the change's own result for as long as it stands. A pre-existing failure is a task, not a disposition.

**How to apply:** `gh run view --log-failed` tells a break the change caused from one it inherited. Fix it — see [solving-what-a-session-finds](solving-what-a-session-finds.md). A failing `sv-tests-coverage` job in `.github/workflows/deltahdl.yml` is no exception: the user asked on 2026-09-23 that it be treated like any other red run, where it had been ignored while sv-tests failed.
