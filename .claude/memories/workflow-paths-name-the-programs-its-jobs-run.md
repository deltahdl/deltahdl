---
name: workflow-paths-name-the-programs-its-jobs-run
description: "A workflow's on.push.paths filter names every tree holding a program its jobs run, the Python trees included, or a change to that program never meets the job that runs it."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:55.121Z
---

# A workflow's paths name the programs its jobs run

`.github/workflows/deltahdl.yml` watches the Python trees its jobs run as well as the C++ ones: `lib/python/run_tests_common/`, `scripts/run_integration_tests/`, `scripts/run_sim_tests/` and `scripts/run_sv_tests/` for the integration and e2e jobs, and `scripts/assert_subclause_citations/` for `assert-subclause-citations`.

**Why:** The unit tests of those programs run in `.github/workflows/scripts.yml`. Without the entries, a change to one of them would be exercised by its unit tests alone and never by the job that runs it.

**How to apply:** When a job in a workflow starts running a program from another tree, add that tree to the workflow's `paths` filter in the same commit, and add it to the tree list of the workflow's `assert-no-comments` job, which mirrors the filter.
