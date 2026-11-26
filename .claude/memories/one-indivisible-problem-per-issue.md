---
name: one-indivisible-problem-per-issue
description: "An issue of a standard holds one rule that deltahdl breaks or leaves untested, or one part of such a rule small enough for one push, with every case of it listed; any other issue holds one defect with one fix. Two rules or two parts are split, and issues holding the same cases are merged."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T14:38:11.773Z
---

# One indivisible problem per issue

An issue holds one problem and no more.

- **An issue of a standard** holds one rule the standard states that deltahdl breaks or leaves untested, or one part of such a rule when the rule's cases need more than one push. A part is the cases of one form, of one kind of place such as a package or a class, or of one kind of operand or type, whichever divides the fix best; a forbidden form stays with its nearest allowed form. The issue lists every case of its rule or part, meaning each allowed and forbidden form in each place it can be written ([fixing-a-rule-in-full](fixing-a-rule-in-full.md)), and names the issues of the rule's other parts. Two rules are two issues, even when they share a clause, a failing file list or a first report. Two cases of one part are one issue, even when they were found apart.
- **An issue about deltahdl itself**, such as a coverage gap or a harness defect, holds one defect with one fix.

This holds when filing and when reading:

- An open issue found holding two rules, or more of a rule than one push takes, is split on the spot, before its code is written or partway through. The existing number is kept for the rule or part its title leads with, and each other rule or part moves to a new issue, filed before more code is written, so that together they list every case the issue listed.
- Open issues found holding cases of one part are merged into the lowest-numbered of them, and the others are closed as duplicates of it.
- The tracker that counts them (#3640 and its like) is adjusted to match.

**Why:** An issue holding two rules never closes cleanly: it sits open while half its content is done, its title says less than its body, and nothing in the tracker says which half is left. An issue holding one case of a rule closes too soon: its fix reaches that case, and the rule's other cases, on record nowhere, surface later as a chain of issues. An issue holding the whole of a large rule grows past what one session holds in view: its fix runs to dozens of files, each edit rebuilds and reruns everything the fix touches, and the coverage and lint findings arrive all at once at the end.

**How to apply:** Ask of each finding which rule it breaks, and which part of it. Where an issue of that part is open, add the finding to it as a case. Where none is, list every case of the rule and open an issue for each part that holds one not yet on record. Two symptoms of one defect stay together: a split divides rules and their cases, not file lists.
