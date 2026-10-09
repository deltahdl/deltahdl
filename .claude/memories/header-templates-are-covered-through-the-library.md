---
name: header-templates-are-covered-through-the-library
description: a unit test that instantiates a src/ header template with its own lambda earns no assert-coverage credit; reach the guard through a library caller
metadata:
  node_type: memory
  type: feedback
  originSessionId: 0ce081b6-fd14-4da5-87da-08ca53aae436
  modified: 2026-10-09T00:22:46.004Z
---

`assert-coverage` runs `llvm-cov` over `libdeltahdl_lib.so` and the `deltahdl` executable only. A unit test that calls a template from a `src/` header with a lambda or type of its own instantiates that template in the test binary, which the report never reads, so the branches the test takes stay uncovered. An exported non-template function the test calls is the library's own copy and does count.

**Why:** the tests first written for `vpi_design_walk.h`'s walk guards called `WalkInstancePaths` and `WalkInstanceObjects` directly with test lambdas, and five of six branches stayed untaken until a test handed `VpiContext::Attach` hand-built designs so the library's instantiations walked them.

**How to apply:** to cover a guard in a header template, find the library function that instantiates it and drive that with inputs that reach the guard; a direct call is a behaviour test, not a coverage one. Related: [[verifying-through-ci]], [[braced-case-closing-brace-is-a-line]].
