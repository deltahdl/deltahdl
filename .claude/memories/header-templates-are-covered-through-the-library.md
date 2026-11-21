---
name: header-templates-are-covered-through-the-library
description: a unit test that instantiates a src/ header template with its own lambda earns no assert-coverage credit; reach the guard through a library caller
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-11-21T02:52:40.116Z
---

# Header templates are covered through the library

`assert-coverage` runs `llvm-cov` over `libdeltahdl_lib.so` and the `deltahdl` executable only. A unit test that calls a template from a `src/` header with a lambda or type of its own instantiates that template in the test binary, which the report never reads, so the branches the test takes stay uncovered. An exported non-template function the test calls is the library's own copy and does count. The file summary also credits a template's branches from its single best-covered instantiation, never the union: two branches each taken by a different instantiation still leave one counted as missed.

**Why:** the gate counts only what the library and the executable run, so a guard in a header template is covered only when one of their own instantiations takes it, and a branch is counted as taken only when a single instantiation takes it.

**How to apply:** to cover a guard in a header template, find the library function that instantiates it and drive that with inputs that reach the guard; a direct call is a behaviour test, not a coverage one. When `llvm-cov show` lists every branch taken somewhere and the summary still counts one missed, give one caller an input that takes all of them at once. Related: [verifying-through-ci](verifying-through-ci.md), [braced-case-closing-brace-is-a-line](braced-case-closing-brace-is-a-line.md).
