---
name: one-indivisible-problem-per-issue
description: "An issue holds one problem: one thing deltahdl gets wrong or leaves untested that one fix corrects, listing every case that fix corrects. A problem is not a rule, and one rule can hold several. An issue holding two problems is split, and issues holding one problem are merged."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 86699205-8167-4d43-95d1-668dd7cf1a13
  modified: 2026-10-28T14:38:11.773Z
---

# One indivisible problem per issue

An issue holds one problem: one thing deltahdl gets wrong, or leaves untested, that one fix corrects. A problem is not a rule. A rule is what a standard requires, and one rule can hold several problems, such as a forbidden form that the parser lets through inside a class and the elaborator lets through inside a package.

- **An issue of a standard** holds one problem under a rule the standard states. It lists every case of the rule that its fix corrects, each form in each place it can be written ([fixing-a-rule-in-full](fixing-a-rule-in-full.md)), with each forbidden form beside its nearest allowed form, and names the issues of the rule's other problems.
- **An issue about deltahdl itself**, such as a coverage gap or a harness defect, holds one defect with one fix.

Two problems are two issues, even under one rule, and even when they share a clause, a failing file list or a first report. Two cases that one fix corrects are one issue, even when they were found apart. One problem takes one fix, so its issue closes in one push.

This holds when filing and when reading:

- An open issue found holding two problems is split when that is found, before its code is written or partway through. The existing number is kept for the problem its title leads with, and each other problem moves to an issue of its own, filed before more code is written, so that together they list every case the issue listed.
- Open issues found holding one problem are merged into the lowest-numbered of them, and the others are closed as duplicates of it.
- The tracker that counts them (#3640 and its like) is adjusted to match.

**Why:** An issue holding two problems never closes cleanly: it sits open while one is fixed, its title says less than its body, and nothing in the tracker says which is left. An issue holding one case of a problem closes too soon: its fix reaches that case, and the other cases the same fix should reach, on record nowhere, surface later as a chain of issues. Measuring an issue by the rule mixes the two: a rule holding several problems becomes an issue that never closes cleanly, and cutting it down to what fits in a push divides it by size rather than by what is wrong.

**How to apply:** Ask of each finding what deltahdl gets wrong and which fix corrects it. Where an open issue holds that problem, add the finding to it as a case. Where none does, list every case of the rule, see which problem each falls in, and open an issue for each problem not yet on record. Two symptoms of one defect stay together: a split divides problems, not file lists.
