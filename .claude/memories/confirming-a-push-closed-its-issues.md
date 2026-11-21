---
name: confirming-a-push-closed-its-issues
description: "GitHub can leave every issue a pushed commit names with Closes open, so a push's closes are checked and made by hand where they did not take."
metadata:
  node_type: memory
  type: project
  originSessionId: e10149e7-3409-4014-9cb5-13a14e355d4b
  modified: 2026-11-21T02:52:52.107Z
---

# Confirming that a push closed its issues

GitHub can accept a commit on `main` without acting on any of its `Closes #N` lines. A message naming 64 issues in 103 KB has closed none of them, while one naming 19 in 27 KB closed all of its issues; whether the count or the size is at fault is not known.

**Why:** An issue left open after its fix landed looks unsolved, so a later loop takes it up again and works on code that already satisfies it ([closing-keywords](closing-keywords.md)).

**How to apply:** Once a push's runs are clean, check that every issue its message closes is closed. Close any still open with `gh issue close N --reason completed`, commenting which commit solved it. Keep a message that closes several issues to one paragraph per issue rather than a subject that joins dozens of clauses.
