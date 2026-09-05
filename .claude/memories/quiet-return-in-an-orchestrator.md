---
name: quiet-return-in-an-orchestrator
description: The oversize-cycle handler was written with a quiet `return` so the run could continue, and the user corrected it on 2026-04-27.
metadata:
  type: feedback
---

# The oversize-cycle handler that returned quietly

On 2026-04-27 the oversize-cycle handler was implemented with a quiet `return`, so the orchestrator could carry on to the next descendant after hitting the fatal condition. The user corrected it: a silent partial-success run disguises the failure, spends tokens on unrelated downstream work, and leaves it ambiguous whether the run finished.

Supports [failing-loudly](../rules/failing-loudly.md).
