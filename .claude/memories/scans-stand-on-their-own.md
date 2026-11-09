---
name: scans-stand-on-their-own
description: "A scan's result is never hidden behind another scan; no scanning job needs another or a path detector, and each step that reports findings of its own carries if !cancelled()."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:51.068Z
---

# Scans stand on their own

Each scanning job and step in the workflows reports its own result, whatever any other scan found.

**Why:** A job or step that never ran reports neither green nor red, so a breach left standing in the first scan hides every scan behind it for as long as it stands. When the yamllint job sat behind a pair of jobs that decided from the changed paths whether linting was needed, a push touching neither the workflow nor `etc/clang_tidy/` skipped it. Running a scan on every run costs one runner and answers the question in the run graph.

**How to apply:**

- No scanning job lists another scanning job, or a job that decides from the changed paths, in its `needs:`.
- In a job that runs several scans in a row, every step that reports findings of its own carries `if: ${{ !cancelled() }}`, as the markdownlint and yamllint jobs do. The job still fails when any one of them fails, and one run names every breach.

Related: [ci-shows-all-output](ci-shows-all-output.md), [failing-loudly-in-orchestrators](failing-loudly-in-orchestrators.md).
