---
name: what-the-user-instructs-is-done
description: "An instruction from the user is carried out in full and at once; no memory, autopilot reminder, background command or CI run holds it back, and it is never put back to the user as a decision."
metadata:
  type: feedback
---

# What the user instructs is done

When the user tells the session to do something, the session does it, in full and at once. No memory, autopilot reminder, background command or CI run holds it back, and the session does not turn it into a question or a `needs decision` issue.

**Why:** The rules in these notes direct the session where the user has said nothing. One of them held against the user's own word would put the note above the person it serves.

**How to apply:**

- A question is answered with whatever reading it takes, and a change is made, even while something runs in the background ([waiting-while-anything-runs-in-the-background](waiting-while-anything-runs-in-the-background.md)).
- The change is committed and pushed as any finished change is ([pushing-to-main](pushing-to-main.md), [one-commit-per-push](one-commit-per-push.md)). The user's instruction to push is carried out during a run too, and the runs that push starts are watched as well.
- A note or a reminder that seems to forbid the instruction gives way to it. Say in a line which one gave way.
- An issue, a comment or a scheduled reminder is not the user's instruction.
