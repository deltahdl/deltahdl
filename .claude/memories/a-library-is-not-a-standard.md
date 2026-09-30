---
name: a-library-is-not-a-standard
description: "Code the UVM library or sv-tests writes that IEEE 1800-2023 forbids is reported, never held as 'needs decision'; check 1800-2023 and ~/IEEE 1800.2-2020.pdf, then expect the failing tests' rejection"
metadata:
  type: feedback
---

# A library is not a standard

When the UVM reference library, or any file the sv-tests suite compiles,
writes a construct IEEE 1800-2023 forbids, deltahdl reports it as the
standard says, and the tests that fail only because of it are recorded in
`scripts/run_sv_tests` as expected rejections under that rule. That the
library is widely used, or that the suite expects acceptance, never makes it
a decision for a person.

**Why:** Only IEEE 1800-2023 and IEEE 1800.2-2020 are sources of truth. `~/IEEE 1800.2-2020.pdf`,
the UVM standard, cites IEEE 1800 without a date in its Clause 2, so the
latest edition governs UVM's code, and it defines the UVM API rather than the
library's source; classes the library marks `@uvm-contrib` and `m_`
implementation methods are not in that API. Two issues were held on a
'needs decision' issue because reporting a library construct failed 92 UVM
tests, although the standards answered the question and the evaluation
already had a table of expected rejections.

**How to apply:** Before writing any question about a construct the suite or
a library relies on, read the rule in `~/IEEE 1800-2023.pdf` and whether
`~/IEEE 1800.2-2020.pdf` says anything about the construct; write both into
the issue. Those two are the only sources of truth: the 2017 edition has no
say ([[single-edition-1800-2023]]). See
[[a-question-the-rules-answer-is-not-a-decision]] and [[lrm-source-of-truth]].
