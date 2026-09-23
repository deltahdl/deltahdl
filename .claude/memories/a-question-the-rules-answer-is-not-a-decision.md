---
name: a-question-the-rules-answer-is-not-a-decision
description: "Before labelling an issue 'needs decision', check whether the standing reminders, the issue or the LRM already answer the question; if one does, act on it"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0eac2fc8-aa5f-4f95-9fa7-69e4f3f0a42a
  modified: 2026-09-23T02:25:43.464Z
---

# A question the rules answer is not a decision

An issue is labelled 'needs decision' only for a question that the autopilot
skill's standing reminders, the issue itself, the linked issues and the LRM
all leave open. A question they answer is acted on, with its answer and what
the answer rests on written into the issue.

**Why:** On 2026-09-22 the user asked of #2929, "what decision does 2929 need
to made? knowing what the reminders tell you and what the issue says. can you
make the right decision that is not a guess?" The issue had waited on whether
to take the §8.25 refactor, #3774, ahead of the non-UVM work. The reminder to
solve whatever issues the original one depends on already answered that, and
#3774 had since closed anyway.

**How to apply:** Before writing a question for a person, test it against each
reminder and against the blocked-by links. Questions of order or priority
between issues the loop selects are answered that way. Once the answer stands,
state it per [[issues-state-conclusions-not-the-trail]] and remove the label.
