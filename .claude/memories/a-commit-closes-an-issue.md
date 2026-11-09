---
name: a-commit-closes-an-issue
description: "Every commit closes at least one issue, as many as it finishes, wherever in the repository they fall, every case of each one's rule passing; an issue too large for one commit is split by rule before its work starts."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-08T17:41:51.536Z
---

# A commit closes at least one issue

Every commit closes at least one issue. It closes as many as it finishes, such as a group of issues whose fixes go through the same code, and the issues may fall anywhere in the repository: source, tests, scripts, workflows, documentation or the notes. Every case of the rule of each issue it closes passes in that commit. When an issue's open cases cannot all land in one commit, it is split by rule before its work starts, per [one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md), so that each part closes with the commit that finishes it. Only a second rule leaves the issue: a case of a rule it already documents stays in it, per [what-does-not-get-filed](what-does-not-get-filed.md).

**Why:** A string of commits that each reference an issue and none closes it leaves a rule half fixed on `main`, its cases never tested together as [fixing-a-rule-in-full](fixing-a-rule-in-full.md) asks, and the open issue list stops saying what is still wrong.

Two kinds of commit close nothing:

- the fix for a red run of the session's own push, which goes in a push of its own per [fixing-a-red-run](fixing-a-red-run.md);
- a change the user asks for directly.

Something found and fixed on the spot along the way rides in a commit that closes an issue.

**How to apply:** Before starting an issue's work, check that every open case of its rule can land in one commit, and split the issue by rule when they cannot. Write `Closes #N` on its own line for each issue the commit finishes, per [closing-keyword-form](closing-keyword-form.md) and [one-closing-keyword-per-issue](one-closing-keyword-per-issue.md), and `Refs #N` only for another issue it touches without finishing. After the run, [confirming-a-push-closed-its-issues](confirming-a-push-closed-its-issues.md).
