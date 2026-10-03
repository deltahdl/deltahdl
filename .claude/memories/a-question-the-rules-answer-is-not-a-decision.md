---
name: a-question-the-rules-answer-is-not-a-decision
description: "Before labelling an issue 'needs decision', check whether the standing reminders, the issue or the standards (1800-2023 and 1800.2-2020, and the clauses that cite or parallel the rule) already answer the question; if one does, act on it"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 51a015a3-4652-42ac-8c15-ce1bc6f6ae12
  modified: 2026-10-03T01:52:38.467Z
---

# A question the rules answer is not a decision

An issue is labelled 'needs decision' only for a question that the autopilot
skill's standing reminders, the issue itself, the linked issues and the
standards all leave open. A question they answer is acted on, with its answer and what
the answer rests on written into the issue.

**Why:** A question the rules already answer has its answer; labelled 'needs
decision', it parks the issue on a person who can only restate that answer.
Questions of order are the usual case: the reminder to solve whatever issues
the original one depends on answers them.

**How to apply:** Before writing a question for a person, test it against each
reminder and against the blocked-by links. For a question of what the language
allows, read the rule in both standards, `~/IEEE 1800-2023.pdf` and
`~/IEEE 1800.2-2020.pdf`, and write what each says into the issue, pages
included; the 2017 edition is no source of truth ([[the-2017-edition]]).
Read beyond the clause itself too: the clause that states the parallel rule
for a sibling construct, and every clause that cites this one, often settle
a reading the clause alone leaves open, as §16.3's grant for immediate
assertions and §17.3's use of the §16.14 list settle that §16.14's list of
places is the whole grant. Questions of order or priority
between issues the loop selects are answered that way. A concern the
standard does not raise, such as the hazard of loading a library a source
file names under §34.5.28.2, does not make a shall optional: the shall is
implemented and the concern, if worth keeping, is filed as its own issue.
Test the question's premise as well as its options: when it asks how two
of deltahdl's own entities relate, first check that the standard defines
both. If one is only an artifact of the implementation, the standard does
not leave the question open; the question does not arise, and the issue is a
defect. For example, §19.9 loads coverage per covergroup type, so "is a saved
instance the same as the live instance of its name" has no standard answer to
lack. Once the answer stands,
state it per [[issues-state-conclusions-not-the-trail]] and remove the label.
