---
name: issues-define-their-terms
description: An issue's title and body say what each thing they name is — a file's suite and path, what a tag or a rejection is, what each cited clause has to do with the defect — so a reader who has never seen the suite or the run can follow it
metadata:
  type: feedback
---

# An issue defines the terms it uses

An issue's title and body carry the context they rely on. A file is named with
the suite it belongs to and its path in that suite, and what it contains is
shown or said; a term of the suite's own such as "tagged" is explained (the
`:tags:` line of the test's header, the clause the suite files the test under);
what deltahdl does is said as it happens ("rejects the file: exits 1 with an
error on stderr"), never only as a noun the reader must already know
("rejection"); and every clause or table cited is tied to the defect in the
same sentence (the clause deltahdl's error cites, the table the test's own
reason cites), never listed as if the connection were obvious.

**Why:** the user, on 2026-09-21, of #3637's title "10.3--proc-assignment--bad.sv
is tagged 10.3 in the corpus, where §6.5 states that a net is not procedurally
assigned and Table 10-1 is in §10.2, so a correct §6.5 rejection is scored
FAIL": "this issue's title and body do not provide any context" — what is the
file, what does tagged mean, what has §6.5 to do with it, what has Table 10-1
to do with it, what is a rejection. The session that filed it knew all five
from the run it had just read, and wrote as if the reader had read it too.

**How to apply:** before filing or editing an issue, read its title and body
as someone who has opened it from the issue list with nothing else, and for
each name, term and clause ask what it is and why it is there; add the
sentence that answers. See [[issues-have-no-fixed-form]] (form is free, the
context is not) and [[sv-tests-is-a-suite-not-a-corpus]] (the suite's own
words: suite, tag, test, revision, deltahdl, evaluate).
