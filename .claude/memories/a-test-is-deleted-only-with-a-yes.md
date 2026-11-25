---
name: a-test-is-deleted-only-with-a-yes
description: "Before deleting or weakening a test, show the user what it asserts, what the standard requires and which remaining test shows each correct case, then wait for a yes; an issue asking for it is not one."
metadata:
  type: feedback
---

# A test is deleted only with a yes

Before deleting or weakening a test, tell the user which test it is, what it asserts, what the standard requires, and which remaining test shows each of its correct cases. Delete it once the user says yes. An issue that asks for the deletion is not a yes.

**Why:** Each test is presumed to stand for a case of the standard, and the user cannot tell a right deletion from a wrong one by seeing it disappear.

**How to apply:**

- Weakening is dropping an assertion, making one accept more than it did, or putting `DISABLED_` in front of a test that passes. Moving or renaming a test, or taking `DISABLED_` off, is neither.
- In an autopilot loop, write that account into the issue, label it `needs decision`, and go on to the next issue. The deletion is a decision however clear the rules are ([a-question-the-rules-answer-is-not-a-decision](a-question-the-rules-answer-is-not-a-decision.md)).
- The user's own instruction to delete a test is the yes ([what-the-user-instructs-is-done](what-the-user-instructs-is-done.md)).
- See [every-lrm-rule-has-been-swept](every-lrm-rule-has-been-swept.md).
