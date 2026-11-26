---
name: a-push-closes-an-issue
description: "Every push closes at least one issue, and as many more as its work finishes; the commits inside it may be steps that close nothing; an issue too large for one push is split first, by rule and then by part of a rule; only a red-run fix or a change the user asks for may close none."
metadata:
  node_type: memory
  type: feedback
  originSessionId: be53c13f-03bb-4ddf-b834-c4e0b8cde655
  modified: 2026-11-26T15:06:27.368Z
---

# A push closes at least one issue

Every push closes at least one issue. It may close as many as its work finishes, with no upper limit: issues whose fixes go through the same code, or unrelated ones, in source, tests, scripts, workflows, documentation or the notes. Issues that are close to done join the push rather than waiting for a later one. An issue whose open cases need more than one push is split by rule, and then by part of a rule, before its work starts, or partway when that is found then ([one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md)).

A push carries one commit or several, as the session chooses ([commits-in-a-push-are-the-sessions-choice](commits-in-a-push-are-the-sessions-choice.md)). A commit may finish an issue or only move one forward; it is the push, taken as a whole, that has to finish at least one. This says what a push holds, not when it goes: the session chooses when to push.

**Why:** CI checks a push at its head, so the push is what lands on `main` checked. A string of pushes that each reference an issue and none closes it leaves an issue half fixed on `main`, its cases never tested together as [fixing-a-rule-in-full](fixing-a-rule-in-full.md) asks, and the open issue list stops saying what is still wrong. Inside one push that risk does not arise, since all its commits land and are checked together.

Two kinds of push may close nothing:

- the fix for a red run of the session's own push, which goes in a push of its own per [fixing-a-red-run](fixing-a-red-run.md) and writes `Refs #N` on its own line for every issue whose tests it changes;
- a change the user asks for directly.

**How to apply:** Before starting an issue's work, check that every case it lists can land in one push, and split the issue when they cannot. Write `Closes #N` on its own line in the commit that finishes issue N, per [closing-keywords](closing-keywords.md), and `Refs #N` in each earlier commit of the push that works on it without finishing it. A finding related to the push's issues rides in that push, and any other is filed ([what-does-not-get-filed](what-does-not-get-filed.md)). After the run, [confirming-a-push-closed-its-issues](confirming-a-push-closed-its-issues.md).
