---
name: vpi-error-status-is-read-alone
description: "A C test program reads vpi_chk_error() into a local in a statement of its own, right after the call it checks; passed as an argument beside another VPI call, it may read that call's status instead."
metadata:
  node_type: memory
  type: project
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:37:38.943Z
---

# The VPI error status is read in a statement of its own

The C programs under `test/src/e2e/` that check whether a VPI call failed read `vpi_chk_error(0)` into a local in a statement of its own, right after that call, and print the local later. `vpi_acceptance_19_put_value_delay_modes.c` and `vpi_acceptance_22_put_value_classdefn_var_illegal.c` both work this way.

**Why:** Every VPI routine other than `vpi_chk_error` resets the error status (IEEE 1800-2023 §38.2), and C leaves the order in which a call's arguments are evaluated unspecified. If the read is one argument of a `vpi_printf` that also calls `vpi_get(...)` or `str_of(...)`, the other call may run first and clear the status. The test then reports the error on one compiler and no error on another.

**How to apply:** When a program prints an error flag beside the result of another VPI call, read the flag into a local first. Folding the local back into the `vpi_printf` arguments to save a line brings back the dependence on argument order. A `vpi_chk_error(0)` passed as an argument is safe only when no other argument calls a VPI routine. Related: [[vpi-design-run-setup]].
