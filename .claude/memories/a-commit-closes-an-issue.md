---
name: a-commit-closes-an-issue
description: "Every commit closes at least one issue, and as many more as its work finishes, wherever in the repository they fall, every case each one lists passing; an issue too large for one small commit is split first, by rule and then by part of a rule; only a red-run fix or a change the user asks for may close none."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-21T02:54:07.352Z
---

# A commit closes at least one issue

Every commit closes at least one issue. It may close as many as the work finishes together, with no upper limit: issues whose fixes go through the same code, or unrelated ones, in source, tests, scripts, workflows, documentation or the notes. Issues that are close to done join the same push, in commits of their own or together in one ([several-commits-per-push](several-commits-per-push.md)), rather than waiting for a later push. Every case each issue it closes lists passes in that commit; for an `lrm-tests` issue, which asks for tests alone, every test it asks for is in it ([lrm-tests-issues-are-tests-only](lrm-tests-issues-are-tests-only.md)). An issue whose open cases need more than one small commit is split by rule, and then by part of a rule, before its work starts, or partway when that is found then ([one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md)).

**Why:** A string of commits that each reference an issue and none closes it leaves an issue half fixed on `main`, its cases never tested together as [fixing-a-rule-in-full](fixing-a-rule-in-full.md) asks, and the open issue list stops saying what is still wrong.

Two kinds of commit may close nothing:

- the fix for a red run of the session's own push, which goes in a push of its own per [fixing-a-red-run](fixing-a-red-run.md) and writes `Refs #N` on its own line for every issue whose tests it changes;
- a change the user asks for directly.

**How to apply:** Before starting an issue's work, check that every case it lists can land in one small commit, and split the issue when they cannot. Write `Closes #N` on its own line for each issue the commit finishes, per [closing-keywords](closing-keywords.md), and `Refs #N` only for another issue it touches without finishing. A defect fixed on the spot along the way ([what-does-not-get-filed](what-does-not-get-filed.md)) rides in a commit that closes an issue. After the run, [confirming-a-push-closed-its-issues](confirming-a-push-closed-its-issues.md).
