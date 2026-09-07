---
name: lrm-source-of-truth
description: ~/LRM.pdf (IEEE 1800-2023) decides what the code must do; where a linter and the standard disagree, the standard wins.
metadata:
  type: feedback
---

# The LRM is the source of truth

Check any change beyond pure cosmetics against `~/LRM.pdf`, and do not let it conflict with what the clause says. `~/LRM.pdf` is a symlink to IEEE 1800-2023, the SystemVerilog standard, and it decides what deltahdl implements.

**Why:** Mechanical lint fixes — enum base types, value initialisation, `auto`, boolean simplification — are behaviour-preserving and carry no risk. Deeper fixes do: resolving compile errors, collapsing a duplicate `CoverageControl` enum, renaming VPI or DPI functions. The standard mandates the VPI names (`vpi_printf`, `vpi_mcd_*`) and the §40.3 coverage-control constants, so satisfying a linter by renaming them breaks the conformance the project exists to achieve.

**How to apply:** Read the relevant clause before making a non-cosmetic change — [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md) and [locating-a-clause](locating-a-clause.md) carry how. When a linter and the standard disagree, say so rather than quietly breaking conformance.
