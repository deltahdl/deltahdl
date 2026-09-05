# The LRM is the source of truth

Check any change beyond pure cosmetics against `~/LRM.pdf`, and do not let it conflict with what the clause says. `~/LRM.pdf` is a symlink to IEEE 1800-2023, the SystemVerilog standard, and it decides what deltahdl implements.

Mechanical lint fixes — enum base types, value initialisation, `auto`, boolean simplification — are behaviour-preserving and carry no risk. Deeper fixes do carry risk: resolving compile errors, collapsing a duplicate `CoverageControl` enum, renaming VPI or DPI functions. The standard mandates the VPI names (`vpi_printf`, `vpi_mcd_*`) and the §40.3 coverage-control constants, so satisfying a linter by renaming them breaks the conformance the project exists to achieve. When the linter and the standard disagree, surface the conflict.

The standard also guides how code is structured, not only what it does. When a refactor groups a function's parameters into a struct — to satisfy a parameter-count threshold, say — mirror the entities the standard defines for that feature. `$readmem` in §21.4 is a file, plus a target memory (an unpacked array with an element type, per §7.4.3, §21.4.1 and §21.4.2), plus an optional start and finish window. So the parameters belong in a `MemTarget` and a `LoadWindow`, not in one struct of leftovers. The clause citations already in the code comments are the guide to the right grouping.
