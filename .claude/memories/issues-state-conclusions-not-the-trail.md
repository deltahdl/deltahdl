---
name: issues-state-conclusions-not-the-trail
description: When a finding settles a question, rewrite the issue to state the answer and drop the alternatives it ruled out; never append each round's reasoning to the last
metadata:
  type: feedback
---

# An issue states the conclusion, not the trail

When a later finding settles a question an issue was weighing, the body is
rewritten to say the answer and what it rests on; the options it ruled out
and the reasoning that ranked them are removed, not kept beside it.

**Why:** the user, on 2026-09-21, of #3637 after five rounds of questions
had each added a paragraph: "why is there so much noise in this issue if the
sv-tests repo is strict about which tag it should be?" The suite's own rule
fixed the tag, which made the three-way comparison of candidate tags and the
cost of each the trail of getting there, not findings.

**How to apply:** after adding a finding, re-read the whole issue and cut
every sentence the finding makes moot. See [[issues-define-their-terms]].
