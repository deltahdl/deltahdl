---
name: lowerbinarybit-default-arm
description: Reading LowerIncDecStmt under #3007 turned up LowerBinaryBit's constant default arm, filed as #3028, #3029 and #3030.
metadata:
  type: project
---

# The finding that arrived while working on something else

Reading `SynthLower::LowerIncDecStmt` into place under #3007 is what showed that `SynthLower::LowerBinaryBit` answers `AigGraph::kConstFalse` for every operator it has no arm for.

That default arm returns a constant for the arithmetic operators, for the comparisons and for the shifts, and it was filed as three issues rather than one — #3028, #3029 and #3030 — because each closes by finishing on its own, and the third does not wait on the first two to be worth reading.

Supports [filing-what-a-session-finds](../rules/filing-what-a-session-finds.md).
