---
name: a-failing-pages-deployment
description: "A failing GitHub Pages deployment of the coverage report is fixed in the repository's Pages settings, never by letting the step fail quietly."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 71fdefb1-3397-48b8-838f-7c5e17be7223
  modified: 2026-11-08T02:13:14.021Z
---

# A failing Pages deployment

When the `Publish to GitHub Pages` step of `assert-coverage` in `.github/workflows/deltahdl.yml` fails, the fix is in the repository's settings: Settings, then Pages, then Source set to "GitHub Actions".

**Why:** The step fails when the repository is not set up to take a deployment from a workflow, and nothing in the workflow can change that. Marking the step `continue-on-error` would hide the failure and leave the coverage report unpublished with a green run.

**How to apply:** Tell the user which setting to change, since it is outside the tree. Leave the step as it is, per [never-weakening-a-gate](never-weakening-a-gate.md).
