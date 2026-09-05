---
name: sv-tests-hypotheses-were-wrong
description: On 2026-07-01 reading an sv-tests failure's source produced two confident hypotheses in a row and both were wrong.
metadata:
  type: project
---

# Two confident wrong hypotheses about one sv-tests file

On 2026-07-01, reading the code to explain a failing sv-tests file produced two confident hypotheses in a row — scalar-versus-queue dispatch, then concat-init-not-lowered — and both were wrong. The actual causes only became visible from the binary's own output.

`print_reason` in `scripts/run_sv_tests/__init__.py` says the same thing in its docstring, which is why the runner prints the tool's output under every FAIL line.

Supports [diagnosing-sv-tests-failures](../rules/diagnosing-sv-tests-failures.md).
