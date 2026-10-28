---
name: solving-what-a-session-finds
description: "A case of the rule in hand joins that fix; file anything else the session finds as issues of one rule or one problem each, and solve one now only if the work in hand cannot move forward without it."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T14:38:16.526Z
---

# Solving what a session finds

A case of the rule an issue in hand documents is part of that issue's fix, never a new issue. File anything else you find as issues of one rule or one problem each ([[one-indivisible-problem-per-issue]]). Solve one now only if the work in hand cannot move forward without it; otherwise move on.

**Why:** This is reminder :08 of `.claude/skills/autopilot/SKILL.md`, and the notes have to say what the reminder says or a session runs under two rules. A case of the rule in hand is fixed in the same commit because its tests and code are already open; filed instead, it would leave the rule half-fixed under a closed issue ([[fixing-a-rule-in-full]]). An issue makes any other finding durable, since the task list and the scratchpad are not ([[research-lives-in-issues]]). Solving every other finding on the spot would pull the session off the work in hand for each one, and a filed issue is picked up by the issue loop in its turn.

**How to apply:** Ask first whether a finding is a case of the rule in hand. If it is, add its test and its fix to the commit in hand. Otherwise file it when it arises, unless an open issue already documents its rule, in which case add the case to that issue ([[what-does-not-get-filed]]). If the work in hand is blocked on it, solve it first, in a push of its own where the grouping rules require one. Otherwise carry on with the work in hand and leave the issue to the loop.
