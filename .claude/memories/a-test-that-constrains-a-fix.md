---
name: a-test-that-constrains-a-fix
description: A case that passes before its fix but fails if the fix takes the wrong route is not redundant with the case that shows the defect; check what wrong implementation a test alone catches before deleting it.
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:19:50.026Z
---

# A test that constrains a fix

A case can exist to rule out a wrong fix rather than to show the defect. It passes before the fix and keeps passing after the right one, and it fails only when the fix takes the wrong route. Such a case stays, even beside a case that looks like it covers the same ground.

**Why:** The case showing a defect is often satisfied by a fix that does too much, such as a lookup that finds nothing at all or an upward reference removed outright. Only the constraining case tells that fix apart from the right one, and it reads as a duplicate to anyone who doesn't ask what it alone would catch.

**How to apply:** Before deleting a test as redundant, name the wrong implementation it alone would fail on. If there is one, keep the test and let its name say what it pins. `InstanceScopeSimulation.LocalNameStillResolvesUnderInstancePrefix` and `InstanceScopeSimulation.HierarchicalNameStillClimbsPastModuleBoundary` in `test/src/unit/test_simulator_subclause_23_09.cpp` are two such cases. The second covers a climb under a lowering prefix, which none of the §23.8 cases in `test_simulator_subclause_23_08.cpp` reaches, because they all run inside an `initial` block. Related: [renaming-rather-than-deleting-a-duplicate-test](renaming-rather-than-deleting-a-duplicate-test.md).
