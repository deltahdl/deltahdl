---
name: sweeping-a-citation-change
description: "Moving a diagnostic's Subclause citation means grepping the message text across the whole tree, not the files named after the old subclause."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:50:54.755Z
---

# Sweeping a citation change

When a diagnostic's `Subclause("…")` moves to another clause, find every assertion that follows it by grepping the message the diagnostic prints, across `src/` and `test/` together. The files named after the old subclause are not the set: one rule is asserted from files named for the clause that states it, from files named for the clause whose shape reaches it, and from the lettered siblings of a split family.

**Why:** A sweep by file name misses the rest of that set, and an assertion it misses still expects the old citation and turns a coverage shard red after the push.

**How to apply:** before committing, run the sweep once more on the message text alone and confirm every hit carries the new clause. See [test-file-letter-suffixes](test-file-letter-suffixes.md) and [naming-the-report-in-a-rejection-test](naming-the-report-in-a-rejection-test.md).
