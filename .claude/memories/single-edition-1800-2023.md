---
name: single-edition-1800-2023
description: deltahdl fulfills IEEE 1800-2023 alone; an older edition's numbering, wording or rule, however it arrives, never reaches deltahdl's behaviour or its reports.
metadata:
  type: feedback
---

# The repository fulfills IEEE 1800-2023 alone

deltahdl conforms to one edition of the standard, the IEEE 1800-2023 that `~/IEEE 1800-2023.pdf` holds. No older edition has any standing here: its clause numbers, its wording and its rules are not what deltahdl implements, cites or is judged against.

**Why:** sv-tests names its files and tags by IEEE 1800-2017, and its file names — `18.5.10--variable-ordering`, `18.5.14--soft-constraints` — carry numbers one above the 2023 headings of the same title (§18.5.9 on physical page 540, §18.5.13 on 547 of `~/IEEE 1800-2023.pdf`). A reader could take the mismatch as a reason to make deltahdl cite the suite's numbers, or to reason from what the 2017 text says. Neither: deltahdl's report cites the 2023 subclause whose rule it enforces, whatever translation the suite needs belongs to the evaluation in the repo's `run_sv_tests` script alone, and the only facts to reason from are the suite's own file names and the 2023 pages. The 2017 text ([[the-2017-edition]]) serves one purpose: judging what an sv-tests tag meant in its own edition, never what deltahdl does.

**How to apply:** When a test suite, an issue, a test name or an external reference uses another edition's numbering, resolve it to the 2023 clause through `~/IEEE 1800-2023.pdf` per [locating-a-clause](locating-a-clause.md) and write the 2023 number; never carry the older number into deltahdl, its messages or its tests. Where the two editions differ in substance, the 2023 text decides, per [lrm-source-of-truth](lrm-source-of-truth.md). Say in the commit or issue that the source used the older numbering, so the next reader is not sent to the wrong clause.
