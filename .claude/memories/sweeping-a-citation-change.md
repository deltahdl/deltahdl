---
name: sweeping-a-citation-change
description: Moving a diagnostic's Subclause citation means grepping the message text across the whole tree, not the files named after the old subclause.
metadata:
  type: feedback
---

# Sweeping a citation change

When a diagnostic's `Subclause("…")` moves to another clause, find every assertion and comment that follows it by grepping the message the diagnostic prints, across `src/` and `test/` together. The files named after the old subclause are not the set: one rule is asserted from files named for the clause that states it, from files named for the clause whose shape reaches it, and from the lettered siblings of a split family, and it is explained in comments in source files that cite it without reporting it.

**Why:** A sweep by file name misses the rest of that set: an assertion it misses still expects the old citation and turns a coverage shard red after the push, and a comment it misses goes on citing the wrong clause with nothing to say so.

**How to apply:** before committing, run the sweep once more on the message text alone and confirm every hit carries the new clause. See [[test-file-letter-suffixes]] and [[naming-the-report-in-a-rejection-test]].
