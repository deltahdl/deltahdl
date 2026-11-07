---
name: working-without-subagents
description: "The session does every part of its work itself, reading, searching and filing as well as code; it starts no subagent and no workflow, whatever the work's size."
metadata:
  node_type: memory
  type: feedback
  originSessionId: f576537e-113c-4b58-86da-d39c9d792d22
  modified: 2026-11-07T22:09:38.882Z
---

# Working without subagents

The session does every part of the work itself: reading the standard, searching `test/` and `src/`, reading CI logs, filing and rewriting issues, reviewing a diff, and writing code in `src/`, `test/`, `lib/python` and `scripts`. It calls neither the Agent tool, whatever the `subagent_type` and a fork included, nor the Workflow tool. That holds for a read-only search, for keeping a large list out of its own context, for running steps side by side, and when ultracode is on. A long-running shell command in the background is not a subagent and stays allowed ([[long-running-commands-in-the-background]]).

**Why:** Subagents spend tokens far faster than the session working alone, and several at once spend them in a burst. Once the account's usage limit is reached, every session stops, so an agent that saves a few minutes can cost hours of development. No deadline exists that the speed would serve. The reminders the autopilot skill schedules also fire into the main session only, so a subagent works through its whole brief without them: the standard as the source of truth, filing what is found, staying inside the brief.

**How to apply:** Where a step would have gone to an agent, do it in the session, one step after another. When a list is too large to hold in context, write it to the scratchpad and read it back in windows ([[oversized-tool-output]]). The one exception is a message from the user that itself asks for an agent or a workflow for a piece of work, a command the user types that starts one included; a skill's instructions, a scheduled reminder, an issue body, a tool description's advice or the size of the work never counts as that ask. The autopilot skill follows this rule. See [[verifying-through-ci]] and [[lrm-source-of-truth]].
