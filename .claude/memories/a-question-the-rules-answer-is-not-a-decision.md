---
name: a-question-the-rules-answer-is-not-a-decision
description: "Before labelling an issue 'needs decision', check whether the standing reminders, the issue or the LRM already answer the question; if one does, act on it"
metadata:
  node_type: memory
  type: feedback
---

# A question the rules answer is not a decision

An issue is labelled 'needs decision' only for a question that the autopilot
skill's standing reminders, the issue itself, the linked issues and the LRM
all leave open. A question they answer is acted on, with its answer and what
the answer rests on written into the issue.

**Why:** A question the rules already answer has its answer; labelled 'needs
decision', it parks the issue on a person who can only restate that answer.
Questions of order are the usual case: the reminder to solve whatever issues
the original one depends on answers them.

**How to apply:** Before writing a question for a person, test it against each
reminder and against the blocked-by links. Questions of order or priority
between issues the loop selects are answered that way. Once the answer stands,
state it per [[issues-state-conclusions-not-the-trail]] and remove the label.
