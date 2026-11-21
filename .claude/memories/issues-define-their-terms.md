---
name: issues-define-their-terms
description: "An issue is written so a session that has never seen the run or the conversation can act on it alone; it says what each file, term and cited clause is and why it is there, and otherwise follows no house layout."
metadata:
  node_type: memory
  type: feedback
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:53:28.902Z
---

# An issue defines the terms it uses

The one test of an issue is whether a session that has never seen this conversation can act on it alone, so its title and body carry the context they rely on:

- the method, the clause and printed page, and the reproduction, inline;
- a file named with the suite it belongs to and its path in that suite, and what it contains shown or said;
- a term of the suite's own such as "tagged" explained (the `:tags:` line of the test's header, the clause the suite files the test under);
- what deltahdl does said as it happens ("rejects the file: exits 1 with an error on stderr"), never only as a noun the reader must already know ("rejection");
- every clause or table cited tied to the defect in the same sentence (the clause deltahdl's error cites, the table the test's own reason cites), never listed as if the connection were obvious.

Beyond that, an issue's layout is free: it takes whatever form serves that reader, whatever shape earlier issues took, apart from opening its sections with headings ([issue-sections-take-headings](issue-sections-take-headings.md)).

**Why:** the session that files an issue knows the run it has just read and writes as if the reader had read it too. A reader who opens the issue from the list has none of that, and cannot act on a file, a term or a clause whose meaning and tie to the defect are left out.

**How to apply:** before filing or editing an issue, read its title and body as someone who has opened it from the issue list with nothing else, and for each name, term and clause ask what it is and why it is there; add the sentence that answers. The substance rules still hold: one indivisible problem per issue ([one-indivisible-problem-per-issue](one-indivisible-problem-per-issue.md)), the standard cited and never quoted ([lrm-text-is-copyrighted](lrm-text-is-copyrighted.md)), and the suite's own words ([sv-tests-is-a-suite-not-a-corpus](sv-tests-is-a-suite-not-a-corpus.md)).
