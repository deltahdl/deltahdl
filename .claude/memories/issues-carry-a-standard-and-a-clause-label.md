---
name: issues-carry-a-standard-and-a-clause-label
description: "An issue about a rule of a standard is labelled with that standard (IEEE 1800-2023, IEEE 1800.2-2020 or IEEE 1735-2023) and, for IEEE 1800-2023, with its clause (§N or Annex X); the clause label alone is not enough"
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-10-09T11:48:15.868Z
---

# Issues carry a standard label and a clause label

Every issue that concerns a rule of a standard gets two labels when it is
filed: the label of the standard it falls under, `IEEE 1800-2023`,
`IEEE 1800.2-2020` or `IEEE 1735-2023`, and, for IEEE 1800-2023, the label of
its clause, `§N` or `Annex X`. An issue about deltahdl itself rather than a
standard's rule, such as an `assert-coverage` gap in one file or a defect in
the test harness, falls under no standard and carries neither.

**Why:** the `§N` and `Annex X` labels are numbered by IEEE 1800-2023 alone,
so a clause label without its standard reads the same for every standard the
project tracks, and the standard label is what filters the issues of one
standard. The clause label's own description names the standard, which made
it look sufficient, and filing with it alone let the standard label drop off
nearly every open issue.

**How to apply:** pass both `--label` flags to `gh issue create`. When
bringing an issue up to date, add whichever of the two is missing. The batch
rule in [[grouping-issues-into-a-push]] still reads the matter from the clause
label.
