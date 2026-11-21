---
name: oversized-tool-output
description: One very large tool result blocks every later tool result in the turn; read large files in bounded windows.
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:55:00.793Z
---

# Avoiding oversized tool output

Read large source files in bounded windows — `Read` with a `limit`, or a search for the specific symbol — rather than as whole-file dumps, and never pair a large read with other calls in the same batch.

**Why:** One very large tool result exhausts the content-filter budget that batched PDF reads also spend ([reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md)). After it trips, every later tool result in the turn renders as `... [truncated]`, and verification depends on reading tool output, so the turn cannot be finished.

**How to apply:** Bound the read, or search for the symbol. A list too large to hold goes to a scratchpad file and is read back in windows.
