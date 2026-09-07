---
name: gate-limits-live-in-tracked-files
description: Some CI gates take their limits from a tracked linter configuration or workflow threshold; check a change by reading that file.
metadata:
  type: feedback
---

# Gate limits live in tracked files

Check a change against a gate's limit by reading the file that carries it.

**Why:** Some gates take their limits from a tracked file rather than from a tool default: a linter configuration under `etc/clang_tidy/`, or a threshold written into a workflow. Reading it is free and local, and it is not the same thing as running the gate, which belongs to CI per [verifying-through-ci](verifying-through-ci.md).

**How to apply:** Find the limit in the tracked file and compare against it. `etc/clang_tidy/src.yml` and `etc/clang_tidy/test_src_unit.yml` are the authority on naming — see [const-local-naming](const-local-naming.md) — and `.github/workflows/deltahdl.yml` carries the file-line cap. The configuration is the authority, not a note about it.
