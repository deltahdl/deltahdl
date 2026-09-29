---
name: writing-code-in-the-main-session
description: "The session writes its own code changes; a subagent receives none of the scheduled reminders, so code is not delegated to one."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 48f0d1c1-72cb-48fa-b4ce-bf630c10a065
  modified: 2026-09-29T00:01:26.276Z
---

# Writing code in the main session

The session that holds the reminders writes the code itself, in `src/`, `test/`, `lib/python` and `scripts`. It does not hand an edit to a subagent.

**Why:** The reminders the autopilot skill schedules fire into the main session only. A subagent never receives them and cannot schedule its own, so it reads the notes once and then works unprompted through the longest stretches of a batch. Those are the stretches the reminders exist to keep on course: the LRM as the source of truth, filing what is found, staying inside the brief.

**How to apply:** Research, write, test and commit in one session. A subagent is still fine for a read-only search whose conclusion comes back to the main session, such as sweeping the tree for a pattern. See [[lrm-source-of-truth]] and [[solving-what-a-session-finds]].
