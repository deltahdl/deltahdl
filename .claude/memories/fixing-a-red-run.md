---
name: fixing-a-red-run
description: Fix a red run in the session that finds it, whoever caused it; a pre-existing failure is a task, not a disposition.
metadata:
  type: feedback
---

# Fixing a red run in the session that finds it

Fix a red run in the session that finds it, whoever caused it.

**Why:** A change is unverified until the jobs that build and test have actually run, and a conclusion of `failure` reads the same whether the change broke something or inherited a break. A skipped job reports neither pass nor fail. So an inherited failure hides the change's own result for as long as it stands. A pre-existing failure is a task, not a disposition.

**How to apply:** `gh run view --log-failed` tells a break the change caused from one it inherited. Fix it — see [solving-what-a-session-finds](solving-what-a-session-finds.md). One standing exception: `.github/workflows/deltahdl.yml` is red on every push because `scripts/run_sv_tests/__init__.py` ends in `sys.exit(min(failed, 1))`, so `sv-tests-coverage` (named `integration-test-coverage` until 2026-09-22) fails while any sv-test does, and 1 of 830 does: 20.4--timeformat.sv, whose issue #2919 was closed as not planned because the file contradicts a shall of §20.4.3.
