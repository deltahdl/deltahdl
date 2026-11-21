---
name: failing-loudly-in-orchestrators
description: "Crash the run when something goes wrong inside an orchestrator under scripts/, rather than skipping the item and carrying on."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:54:33.982Z
---

# Failing loudly in the orchestrator scripts

Crash the run when something goes wrong inside one of the orchestrators under `scripts/`, such as `run_sv_tests` or `run_integration_tests`, rather than skipping the failing item and carrying on.

**Why:** A run that skips what failed and ends green disguises the failure and leaves it unclear whether the run finished at all. A run that ends red forces the question in the run graph.

**How to apply:** Recording what a person needs first is fine and often desirable, such as writing the report file. The very next thing must be a raise, or an exit with a non-zero code. A plain `return` after a fatal condition is almost always wrong here. Reserve quiet returns for a genuine no-op, such as a step that finds nothing to do.
