---
name: single-edition-1800-2023
description: deltahdl fulfills IEEE 1800-2023 alone; an older edition's numbering, wording or rule, however it arrives, never reaches the tool's behaviour or its reports.
metadata:
  type: feedback
---

# The repository fulfills IEEE 1800-2023 alone

deltahdl conforms to one edition of the standard, the IEEE 1800-2023 that `~/LRM.pdf` holds. No older edition has any standing here: its clause numbers, its wording and its rules are not what the tool implements, cites or is judged against.

**Why:** The user said so twice on 2026-09-18, as a standing reminder, while an issue on the sv-tests runner was being brought up to date. That corpus names its files and tags by IEEE 1800-2017, whose §18.5 is numbered differently from 2023's, and a reader could take the mismatch as a reason to make the tool cite the corpus's numbers. It is not: the tool's report cites the 2023 subclause whose rule it enforces, and whatever translation the corpus needs belongs to the runner's scoring alone.

**How to apply:** When a corpus, an issue, a test name or an external reference uses another edition's numbering, resolve it to the 2023 clause through `~/LRM.pdf` per [locating-a-clause](locating-a-clause.md) and write the 2023 number; never carry the older number into the tool, its messages or its tests. Where the two editions differ in substance, the 2023 text decides, per [lrm-source-of-truth](lrm-source-of-truth.md). Say in the commit or issue that the source used the older numbering, so the next reader is not sent to the wrong clause.
