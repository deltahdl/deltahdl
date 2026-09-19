---
name: solving-what-a-session-finds
description: Solve a defect the session finds rather than filing it and moving on; a failing integration or e2e test in deltahdl.yml is the one exception, left where it is.
metadata:
  type: feedback
---

# Solving what a session finds

Solve what you find rather than filing it and moving on. A failing integration or e2e test in deltahdl.yml is the exception: leave that one where it is.

**Why:** This is reminder :08 of `.claude/skills/autopilot/SKILL.md`, and the notes have to say the same thing the reminder says or a session runs under two rules. The file this replaced said the reverse — file the finding, do not ask — and on 2026-09-18 a session solving #3620 followed it and filed #3621, #3622 and #3623 for three defects it had read its way to; the user said that was wrong and that the memory should match the autopilot reminder. A defect written into the tracker waits for a later session to redo the reading that found it, while the session that found it has the reading in hand. The exception is drawn where the reminder draws it: the integration and e2e failures in deltahdl.yml are the standing red that #2910 through #2939 track, and a session sent at those spends itself on what it was not started to fix.

**How to apply:** Finish the work in hand first, then fix the finding in the same session — in the commit in hand where it belongs there, otherwise in a commit of its own — and let its own commit message state it. Nothing is filed for it, which is what [what-does-not-get-filed](what-does-not-get-filed.md) already says of a defect the commit in hand fixes. A finding that cannot be solved in the session is a question for the user, not an issue. Where something is filed regardless — an existing issue to cite, a finding the user asked to have tracked — split it by scope per [one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md).
