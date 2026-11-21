---
name: lrm-guides-structure
description: "When grouping parameters into a struct, mirror the entities the standard defines for that feature."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:50:51.605Z
---

# The standard guides structure, not only behaviour

When a refactor groups a function's parameters into a struct — to satisfy a parameter-count threshold, say — mirror the entities the standard defines for that feature.

**Why:** A struct of leftovers satisfies the threshold and tells the next reader nothing. A struct named for something the standard defines carries the clause's own division into the code, so the grouping stays right as the feature grows.

**How to apply:** Read the clause for the entities it names. `$readmem` in §21.4 is a file, plus a target memory (an unpacked array with an element type, per §7.4.3, §21.4.1 and §21.4.2), plus an optional start and finish window — so the parameters belong in a `MemTarget` and a `LoadWindow`, not in one struct of leftovers. The `Subclause("…")` citations at the code's report sites point to the clauses to read. See [lrm-source-of-truth](lrm-source-of-truth.md).
