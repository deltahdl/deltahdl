---
name: one-action-per-task
description: A task subject that names more than one action is divisible by construction; split it by action before starting, and re-read the subjects, not the intent, when the indivisibility reminder fires.
metadata:
  type: feedback
---

# One action per task

A task on the list names one action. A subject that joins several with "and" — format, stage, commit, push, watch, fix, confirm — is divisible by construction, however much those actions add up to one intent.

**Why:** On 2026-09-20 a task read "format the touched files, stage explicit paths, `git status --porcelain`, commit, push after `gh run list`, watch the run, and fix any job it fails", and the session called it indivisible through several firings of the autopilot reminder that asks for indivisibility, because it judged the task by the intent behind it (verify the commit through CI) rather than by the subject it had written. The user asked how seven sub-tasks could pass as one and why the reminder had not convinced the session otherwise. The reminder is answered by reading the words on the list, not by restating the purpose those words serve.

**How to apply:** When writing a task, or when the indivisibility reminder fires, read each subject and count the actions it names; more than one means a split, one task per action, with the steps already done recorded as completed tasks of their own. A step that may or may not be needed (fix a failing job) is added when the run reports it, not folded into the watching task. See [[recording-what-a-session-learns]].
