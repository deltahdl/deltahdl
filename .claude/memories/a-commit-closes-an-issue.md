---
name: a-commit-closes-an-issue
description: "A commit that changes src/ or test/ for an issue closes at least one issue, every case of its rule passing; an issue too large for one commit is split by rule before its code is written."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 84445ccd-f1b9-420f-afbd-5b1a412da9aa
  modified: 2026-11-08T17:35:16.853Z
---

# A commit closes an issue

A commit that changes `src/` or `test/` for an issue closes at least one issue, and every case of that issue's rule passes in the same commit. When an issue's open cases cannot land in one commit, it is split by rule before any of its code is written, per [[one-indivisible-problem-per-issue]], so that each rule's issue closes with the commit that fixes it. Only a second rule leaves the issue: a case of a rule it already documents stays in it, per [[what-does-not-get-filed]].

**Why:** A string of commits that each reference an issue and none closes it leaves a rule half fixed on `main`, its cases never tested together as [[fixing-a-rule-in-full]] asks, and the open issue list stops saying what deltahdl still gets wrong.

Two kinds of commit close nothing:

- the fix for a red run of the session's own push, which goes in a push of its own per [[fixing-a-red-run]];
- a change the user asks for directly, such as to the memories, the settings or CI.

Something found and fixed on the spot along the way rides in the commit that closes the issue in hand.

**How to apply:** Before writing code for an issue, check that every open case of its rule can land in one commit, and split the issue by rule when they cannot. Write `Closes #N` on its own line for each issue the commit finishes, per [[closing-keyword-form]] and [[one-closing-keyword-per-issue]], and `Refs #N` only for another issue it touches without finishing. After the run, [[confirming-a-push-closed-its-issues]].
