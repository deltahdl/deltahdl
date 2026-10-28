---
name: one-indivisible-problem-per-issue
description: "An issue of a standard holds one rule that deltahdl breaks or leaves untested, with every case of it listed; any other issue holds one defect with one fix. Two rules are split, and issues holding cases of one rule are merged."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T14:38:11.773Z
---

# One indivisible problem per issue

An issue holds one problem and no more.

- **An issue of a standard** holds one rule the standard states that deltahdl breaks or leaves untested. It lists every case of that rule, meaning each allowed and forbidden form in each place it can be written ([[fixing-a-rule-in-full]]). Two rules are two issues, even when they share a clause, a failing file list or a first report. Two cases of one rule are one issue, even when they were found apart.
- **An issue about deltahdl itself**, such as a coverage gap or a harness defect, holds one defect with one fix.

This holds when filing and when reading:

- An open issue found holding two rules is split on the spot. The existing number is kept for the rule its title leads with, and the other rule moves to a new issue.
- Open issues found holding cases of one rule are merged into the lowest-numbered of them, and the others are closed as duplicates of it.
- The tracker that counts them (#3640 and its like) is adjusted to match.

**Why:** An issue holding two rules never closes cleanly: it sits open while half its content is done, its title says less than its body, and nothing in the tracker says which half is left. An issue holding one case of a rule closes too soon: its fix reaches that case, the rule's other cases surface later as issues of their own, and one fault in deltahdl becomes a chain of issues, each paying for a CI run of its own.

**How to apply:** Ask of each finding which rule it breaks. Where an issue of that rule is open, add the finding to it as a case. Where none is, open one that lists every case of the rule. Two symptoms of one defect stay together: a split divides rules, not file lists.
