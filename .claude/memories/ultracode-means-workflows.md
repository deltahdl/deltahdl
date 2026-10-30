---
name: ultracode-means-workflows
description: "The user runs sessions with ultracode on and expects batches of independent work (Reconcile issues, sweeps) to go through workflows and subagents, even after a summary drops the ultracode notice."
metadata:
  node_type: memory
  type: feedback
  originSessionId: 1aee63bc-4d96-458a-9909-fd02916adb67
  modified: 2026-10-30T02:06:02.358Z
---

When the user has ultracode on, independent work such as a clause's Reconcile issues goes through the Workflow tool: one surveying agent per section, a skeptic verifying each drafted issue, then a filing agent. The work is not done solo, one issue after another.

**Why:** a summarized session can lose the system notice that confirms ultracode, and the session then quietly falls back to solo work. The user noticed and asked why no agents or workflows were running.

**How to apply:** if the user says ultracode is on, treat that as the opt-in even when no notice is visible. Batch Reconcile issues by clause into one pipeline (survey → verify → file), and keep only the steps that share state in the main loop: commits, pushes and runs. See [[a-rule-conforms-only-when-tests-show-it]] and [[guarding-an-issue-body-rewrite]] for what the agents are told.
