---
name: issues-carry-a-standard-and-a-clause-label
description: "An issue about a rule of a standard is labelled with that standard (IEEE 1800-2023, IEEE 1800.2-2020 or IEEE 1735-2023) and with its clause in that standard (§N or Annex X); the clause labels belong to no one standard, so neither label is enough alone"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-10-09T12:24:05.641Z
---

# Issues carry a standard label and a clause label

Every issue that concerns a rule of a standard gets two labels when it is
filed: the label of the standard it falls under, `IEEE 1800-2023`,
`IEEE 1800.2-2020` or `IEEE 1735-2023`, and the label of its clause in that
standard, `§N` or `Annex X`. All three standards are divided into numbered
clauses and lettered annexes, so the same rule holds for each. An issue about
deltahdl itself rather than a standard's rule, such as an `assert-coverage`
gap in one file or a defect in the test harness, falls under no standard and
carries neither.

**Why:** the `§N` and `Annex X` labels are shared by the three standards, and
each label's description says only that it is that clause of the standard the
standard label names. The pair is what identifies a clause: `§5` alone could
be Clause 5 of any of them, and the standard label alone cannot place an issue
within its standard.

**How to apply:** pass both `--label` flags to `gh issue create`. When the
clause has no label yet, such as a clause number past the highest one
IEEE 1800-2023 has, create it first with `gh label create` and the same form
of description. When bringing an issue up to date, add whichever of the two is
missing. The batch rule in [[grouping-issues-into-a-push]] reads the matter
from the two labels together.
