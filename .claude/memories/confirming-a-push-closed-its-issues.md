---
name: confirming-a-push-closed-its-issues
description: GitHub can leave every issue a pushed commit names with Closes open, so a push's closes are checked and made by hand where they did not take.
metadata:
  type: project
---

# Confirming that a push closed its issues

GitHub can push a commit to `main` without acting on any of its `Closes #N` lines. A commit naming 64 issues in a 103 KB message closed none of them, while one naming 19 in a 27 KB message closed all of its issues. Whether the count or the size is at fault is not known.

**Why:** An issue left open after its fix landed looks unsolved, so a later loop takes it up again and works on code that already satisfies it ([[issue-closing-keywords-fire-on-push]]).

**How to apply:** Once a push's runs are clean, check that every issue its message closes is closed. Close any still open with `gh issue close N --reason completed`, commenting which commit solved it. Keep a batch's message to one paragraph per issue ([[grouping-issues-into-a-push]]) rather than a subject that joins dozens of clauses.
