---
name: lrm-guides-structure
description: When grouping parameters into a struct, mirror the entities the standard defines for that feature.
metadata:
  type: feedback
---

# The standard guides structure, not only behaviour

When a refactor groups a function's parameters into a struct — to satisfy a parameter-count threshold, say — mirror the entities the standard defines for that feature.

**Why:** A struct of leftovers satisfies the threshold and tells the next reader nothing. A struct named for something the standard defines carries the clause's own division into the code, so the grouping stays right as the feature grows.

**How to apply:** Read the clause for the entities it names. `$readmem` in §21.4 is a file, plus a target memory (an unpacked array with an element type, per §7.4.3, §21.4.1 and §21.4.2), plus an optional start and finish window — so the parameters belong in a `MemTarget` and a `LoadWindow`, not in one struct of leftovers. The clause citations already in the code comments are the guide to the right grouping. See [lrm-source-of-truth](lrm-source-of-truth.md).
