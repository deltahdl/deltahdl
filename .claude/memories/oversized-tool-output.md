---
name: oversized-tool-output
description: One very large tool result blocks every later tool result in the turn; read large files in bounded windows.
metadata:
  type: feedback
---

# Avoiding oversized tool output

Read large source files in bounded windows — `Read` with a `limit`, or a search for the specific symbol — rather than as whole-file dumps, and never pair a large read with other calls in the same batch.

**Why:** One very large tool result exhausts the same content-filter budget that batched PDF reads do. After it trips, every later tool result in the turn renders as `... [truncated]`, and it does not recover within the turn. That matters because verification depends on reading tool output: once the output is blocked, the turn cannot be finished.

**How to apply:** Bound the read, or search for the symbol. If output starts truncating, stop issuing calls and resume in a fresh turn rather than working blind. See [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md) for the other way this budget is spent.
