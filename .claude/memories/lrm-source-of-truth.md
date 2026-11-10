---
name: lrm-source-of-truth
description: "~/IEEE 1800-2023.pdf (IEEE 1800-2023) decides what the code must do and is read before any statement of what a clause requires; where a linter and the standard disagree, the standard wins."
metadata:
  node_type: memory
  type: feedback
  originSessionId: b425c181-0dc9-4105-9628-ad8462acdd57
  modified: 2026-11-10T05:08:17.088Z
---

# The LRM is the source of truth

Check any change beyond pure cosmetics against `~/IEEE 1800-2023.pdf`, and do not let it conflict with what the clause says. `~/IEEE 1800-2023.pdf` is a symbolic link to IEEE 1800-2023, the SystemVerilog standard, and it decides what deltahdl implements.

**Why:** Mechanical lint fixes — enum base types, value initialisation, `auto`, boolean simplification — are behaviour-preserving and carry no risk. Deeper fixes do: resolving compile errors, collapsing a duplicate `CoverageControl` enum, renaming VPI or DPI functions. The standard mandates the VPI names (`vpi_printf`, `vpi_mcd_*`) and the §40.3 coverage-control constants, so satisfying a linter by renaming them breaks the conformance the project exists to achieve.

**How to apply:** Read the relevant clause before making a non-cosmetic change — [reading-the-lrm-one-page-per-call](reading-the-lrm-one-page-per-call.md) and [locating-a-clause](locating-a-clause.md) carry how. When a linter and the standard disagree, say so rather than quietly breaking conformance.

Read the clause as well before stating what it allows, forbids or leaves open, whether in an answer, an analysis or an issue. A statement made from recollection can rest on another edition's text, or on what other tools accept, and then steers the advice built on it the wrong way.
