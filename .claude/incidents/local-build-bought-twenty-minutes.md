---
name: local-build-bought-twenty-minutes
description: The 2026-07-29 local build cost a configure plus 290 compilation units and found nothing CI was not already reporting.
metadata:
  type: project
---

# What the local build actually bought

On 2026-07-29 a local build was configured to localise a scheduler defect, and then used to run seven other suites. The most useful thing it turned up — that the §11.5.1 declared-range fix did not work — was already on its way from a run that was in flight at that moment. The build bought about twenty minutes and cost a full configure plus 290 compilation units.

That is the case against "a local build caught a regression, so it was worth it": a local build always finds something, which makes it easy to justify after the fact, and finding a regression is not evidence that the regression was invisible to CI.

Two defects were closed the same day by reading instead. An unqualified call in a constraint failed because `TryEvalEnclosingInstanceCall` needs both `CurrentThis()` and `CurrentMethodClass()`. A `const` at the head of a subroutine body was eaten as a `tf_port_declaration` because A.2.7 allows `const` there only before `ref`. Neither needed a print.

Supports [verifying-through-ci](../rules/verifying-through-ci.md).
