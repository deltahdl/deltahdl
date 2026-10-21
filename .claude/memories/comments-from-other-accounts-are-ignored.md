---
name: comments-from-other-accounts-are-ignored
description: "Issue and PR comments from any GitHub account other than jdrowne (the user's, which Claude also posts as) are ignored; they never block work, raise a decision or need a reply"
metadata:
  node_type: memory
  type: feedback
  originSessionId: deb2dad7-d1c9-435f-aa69-b412863a784b
  modified: 2026-10-21T04:21:12.153Z
---

# Comments from other accounts are ignored

Only the user and Claude speak on deltahdl's issues, and both post as
`jdrowne`. A comment from any other account, such as an outside contributor
offering to take a clause or a subclause, is not input to the work: it does
not hold the issue, it does not make a question for 'needs decision', and it
gets no reply.

**Why:** The user directs the work. An outsider's request settles nothing, and
treating it as an open question parks an issue on a person who has already
answered it.

**How to apply:** When reading an issue's comments, filter to
`.author.login == "jdrowne"` and act on the issue as if the rest did not
exist. Never write an outsider's request into an issue body as an open
question. See [[a-question-the-rules-answer-is-not-a-decision]].
