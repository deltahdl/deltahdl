---
name: searching-for-an-existing-report-before-filing
description: "before filing \"X is not reported\", grep all of src/ and test/ for the rule's own words, not just the clause's Subclause(\"…\") tag"
metadata:
  node_type: memory
  type: feedback
  originSessionId: dbb14fe5-4f12-40b5-98ca-0948dad60b8a
  modified: 2026-10-13T00:25:00.815Z
---

# Searching for an existing report before filing

Before filing an issue that says deltahdl does not report something, search the whole of `src/` and `test/src/unit/` for words the rule itself uses (e.g. `ANSI`, `non-void`, `return`), not only for diagnostics tagged with the clause being reconciled. A rule is often already enforced under a neighbouring clause (§12.8 for §13.4.1's return-value rule) or in a different subsystem than the one first looked at (the elaborator rather than the parser for §13.5.3's ANSI-only defaults).

**Why:** fixing a rule that is already reported adds a second diagnostic for one construct, which breaks the existing tests of the first and costs a red run and a revert.

**How to apply:** for every candidate "not reported" finding, grep for the rule's key words and for an existing test of the shape before filing; if a report exists, record it as conforming in the reconciliation issue instead. See [[verifying-through-ci]].
