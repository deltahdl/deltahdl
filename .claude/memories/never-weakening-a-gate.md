---
name: never-weakening-a-gate
description: "A red gate is fixed in the code, never by weakening the gate; no threshold lowered, no check or job disabled, no name exempted, no continue-on-error."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:10.564Z
---

# Never weakening a gate

When a gate reports a breach, the code changes and the gate stays as it is.

**Why:** No person reviews the code that lands on `main`. The gates are the only thing between a defect and the tree, and a gate relaxed to let one change through stays relaxed for every change after it.

**How to apply:** Each of these weakens a gate and is never done to make a run green:

- lowering a threshold: the 100% line coverage that `assert-coverage` in `.github/workflows/deltahdl.yml` enforces, the pass bar the sv-tests run holds deltahdl to, `pytest --cov-fail-under=100`, or a size, complexity or naming limit in `etc/clang_tidy/` (a raised limit, a removed prefix, a changed `Case`)
- disabling a clang-tidy check, or a job, such as `assert-no-inline-directives` or `assert-no-linter-config-files`
- adding a name to an `IgnoredRegexp` to get past a naming rule, where renaming the code is the fix
- adding `continue-on-error` to a step, as in [a-failing-pages-deployment](a-failing-pages-deployment.md)

A check is disabled, or a name exempted, only where a standard mandates exactly what the check forbids. The C++ standard's own names and the names IEEE 1800-2023 prints are examples, listed per [standard-names-listed-explicitly](standard-names-listed-explicitly.md), and the commit that does it names the clause. When a rule looks wrong, read the Google C++ Style Guide before touching the configuration. Related: [gate-limits-live-in-tracked-files](gate-limits-live-in-tracked-files.md), [fixing-a-red-run](fixing-a-red-run.md).
