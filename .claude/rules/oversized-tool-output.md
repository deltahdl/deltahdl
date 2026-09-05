# Avoiding oversized tool output

Read large source files in bounded windows — `Read` with a `limit`, or a search for the specific symbol — rather than as whole-file dumps, and never pair a large read with other calls in the same batch.

One very large tool result exhausts the same content-filter budget that batched PDF reads do. After it trips, every later tool result in the turn renders as `... [truncated]`, and it does not recover within the turn.

That matters because verification depends on reading tool output. Once the output is blocked, the turn cannot be finished. If output starts truncating, stop issuing calls and resume in a fresh turn rather than working blind.

Related: [content-filter-budget](../memories/content-filter-budget.md) for the reads that have tripped it.
