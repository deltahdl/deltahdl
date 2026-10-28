---
name: working-without-subagents
description: "The session does all its own work, reading, searching and filing as well as code, one structured task at a time; it starts no subagent and no workflow, whatever the work's size."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
---

# Working without subagents

The session does every part of the work itself: reading the standard, searching `test/` and `src/`, filing and rewriting issues, and writing code in `src/`, `test/`, `lib/python` and `scripts`. It calls neither the Agent tool nor the Workflow tool, not for a read-only search, not to keep a large list out of its own context, and not to run steps side by side. Work runs one task at a time, each written with TaskCreate before it starts and marked with TaskUpdate as it starts and finishes. A long-running shell command in the background is not a subagent and stays allowed ([[long-running-commands-in-the-background]]).

**Why:** Subagents spend tokens fast, and several at once spend them in a burst, while there is no deadline that speed would serve. The reminders the autopilot skill schedules also fire into the main session only, so a subagent works through its whole brief unprompted by them: the standard as the source of truth, filing what is found, staying inside the brief.

**How to apply:** Where a step would have gone to an agent, make it a task and do it in the session. When a list is too large to hold in context, write it to the scratchpad and read it back in windows ([[oversized-tool-output]]). The autopilot skill's section on Reconcile issues follows this rule. See [[lrm-source-of-truth]] and [[solving-what-a-session-finds]].
