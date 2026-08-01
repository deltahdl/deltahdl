# The LRM is the source of truth

`~/LRM.pdf` is a symlink to IEEE 1800-2023, the SystemVerilog standard. It decides what deltahdl implements. Any change beyond pure cosmetics must be checked against it and must not conflict with it.

Mechanical lint fixes — enum base types, value initialisation, `auto`, boolean simplification — are behaviour-preserving and carry no risk. Deeper fixes do: resolving compile errors, collapsing a duplicate `CoverageControl` enum, renaming VPI or DPI functions. The VPI names (`vpi_printf`, `vpi_mcd_*`) and the §40.3 coverage-control constants are mandated by the standard, and satisfying a linter by renaming them breaks the conformance the project exists to achieve. When the linter and the standard disagree, surface the conflict.

The standard also guides how code is structured, not only what it does. When a refactor groups a function's parameters into a struct — to satisfy a parameter-count threshold, say — the structs should mirror the entities the standard defines for that feature. `$readmem` in §21.4 is a file, plus a target memory (an unpacked array with an element type, per §7.4.3, §21.4.1 and §21.4.2), plus an optional start and finish window. So the parameters belong in a `MemTarget` and a `LoadWindow`, not in one struct of leftovers. The clause citations already in the code comments are the guide to the right grouping.
