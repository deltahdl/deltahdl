---
name: a-deleted-test-leaves-its-cases-shown
description: "Before deleting or weakening a test, establish from the clause and the tree what it asserts, what the standard requires and which remaining test shows each of its correct cases; the commit says so."
metadata:
  type: feedback
---

# A deleted test leaves its cases shown

Before deleting or weakening a test, establish what it asserts, what the standard requires, and which remaining test shows each of its correct cases. Say so in the commit that removes it.

**Why:** Each test is presumed to stand for a case of the standard, and one removed without that check can take the only record of its case with it.

**How to apply:**

- Weakening is dropping an assertion, making one accept more than it did, or putting `DISABLED_` in front of a test that passes. Moving or renaming a test, or taking `DISABLED_` off, is neither.
- Read the clause, open each remaining test and trace the code it runs. An issue asking for the deletion settles none of this.
- A correct case no remaining test shows keeps its test, or gets one in the same commit.
- See [every-lrm-rule-has-been-swept](every-lrm-rule-has-been-swept.md) and [a-test-that-constrains-a-fix](a-test-that-constrains-a-fix.md).
