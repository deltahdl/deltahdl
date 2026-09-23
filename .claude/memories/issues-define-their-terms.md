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

**Why:** the session that files an issue knows the run it has just read and
writes as if the reader had read it too. A reader who opens the issue from the
list has none of that, and cannot act on a file, a term or a clause whose
meaning and tie to the defect are left out.

**How to apply:** before filing or editing an issue, read its title and body
as someone who has opened it from the issue list with nothing else, and for
each name, term and clause ask what it is and why it is there; add the
sentence that answers. See [[issues-have-no-fixed-form]] (form is free, the
context is not) and [[sv-tests-is-a-suite-not-a-corpus]] (the suite's own
words: suite, tag, test, revision, deltahdl, evaluate).
