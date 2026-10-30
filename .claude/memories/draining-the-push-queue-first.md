---
name: draining-the-push-queue-first
description: "Push commits that sit committed locally but unpushed before starting new work."
metadata:
  node_type: memory
  type: feedback
---

# Draining the push queue first

Push any commit that sits on local `main` unpushed before starting new work.

**Why:** An unpushed commit is work CI has not checked. Building more on top of it lets it go stale against the tree and buries a red run under the work stacked above it.
