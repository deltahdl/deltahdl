---
name: vpi-design-run-setup
description: "A test fixture deriving from VpiDesignRun that overrides SetUp must call VpiDesignRun::SetUp first, or no VPI model is built"
metadata:
  node_type: memory
  type: project
  originSessionId: 802dda41-bbd7-4f26-b9f9-a5eba57e3279
  modified: 2026-10-05T17:26:02.142Z
---

# A VpiDesignRun SetUp calls the base first

`VpiDesignRun` (lib/cpp/test_fixtures/fixture_vpi_run.h) registers the global VPI context and a PLI system task in its `SetUp`; a run builds its VPI model only when a PLI application is registered. A derived fixture whose `SetUp` override calls `Run(...)` without `VpiDesignRun::SetUp()` first builds no model, and its cases read whatever an earlier case left in the global context, so they pass or fail by test order.

**Why:** such a fixture failed some cases in one CI run and all of them in the next with no relevant code change, which looked like a defect in the code under test.

**How to apply:** prefer calling `Run` in each `TEST_F`; where a shared `SetUp` is wanted, open it with `VpiDesignRun::SetUp();`. Related: [[verifying-through-ci]].
