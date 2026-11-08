---
name: per-module-elaboration-tables-are-listed-twice
description: Each per-module bookkeeping table of the Elaborator is named both in ResetItemElaborationState and in ItemElaborationStateSaver in src/elaborator/elaborator_module.cpp; a new table goes into both.
metadata:
  node_type: memory
  type: project
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:28:56.231Z
---

# Per-module elaboration tables are listed twice

The `Elaborator` keeps per-module bookkeeping tables, such as `declared_names_`, `net_names_` and `cont_assign_targets_`, and `src/elaborator/elaborator_module.cpp` names each one in two places. `ResetItemElaborationState` clears it before a module's items are elaborated. `ItemElaborationStateSaver` moves it aside before a nested elaboration and puts it back afterwards. A table added to the `Elaborator` goes into both, field for field.

**Why:** A table the reset clears but the saver leaves out loses the outer module's entries when a nested module is elaborated. A table the saver keeps but the reset leaves out starts each module with the last module's entries. Neither shows up until a design nests modules, so the build and most tests stay green. The saver also keeps the three scope maps, `typedefs_`, `cu_param_scope_` and `td_array_dims_`, which the reset leaves alone. It copies them before and puts them back after, adding what the nested module recorded to the `all_` tables.

**How to apply:** Adding a per-module table to `Elaborator` means three edits: clear it in `ResetItemElaborationState`, and add a `decltype` field for it to `ItemElaborationStateSaver` with a move in each direction. Before pushing, compare the two lists.
