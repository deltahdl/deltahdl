---
name: one-action-per-task
description: "A task subject that names more than one action is divisible by construction; split it by action before starting, and re-read the subjects, not the intent, when the indivisibility reminder fires."
metadata:
  node_type: memory
  type: feedback
---

# One action per task

A task on the list names one action. A subject that joins several with "and" — format, stage, commit, push, watch, fix, confirm — is divisible by construction, however much those actions add up to one intent.

**Why:** Judged by the intent behind it, any run of steps passes as one action: format, stage, commit, push and watch all serve "verify the commit through CI". The autopilot reminder that asks for indivisibility is answered by reading the words on the list, not by restating the purpose those words serve.

An umbrella verb does not make a subject one action. "Solve #N", "fix X" or "handle Y" names one verb and stands for the unit case, the change, the check that the case fails without it, formatting, the commit, the push and the CI read. Count the steps the subject commits to, not the verbs it spells.

**How to apply:** When writing a task, or when the indivisibility reminder fires, read each subject and count the actions it names; more than one means a split, one task per action, with the steps already done recorded as completed tasks of their own. A step that may or may not be needed (fix a failing job) is added when the run reports it, not folded into the watching task. See [[recording-what-a-session-learns]].
