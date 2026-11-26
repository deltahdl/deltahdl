---
name: job-names-start-with-a-verb
description: "The first word of a new CI job's name is a verb, as in summarize-commits; a composite action's name follows the same form."
metadata:
  node_type: memory
  type: feedback
  originSessionId: be53c13f-03bb-4ddf-b834-c4e0b8cde655
  modified: 2026-11-26T14:58:42.472Z
---

# Job names start with a verb

The first word of a new job's name under `.github/workflows/` is a verb saying what the job does, as in `summarize-commits` or `assert-no-comments`. A composite action under `.github/actions/` is named the same way, as in `install-llvm`.

**Why:** The user asked for it. A verb first tells a reader of the run page what the job does, not only what it is about. This follows from [names-say-what-a-thing-does](names-say-what-a-thing-does.md).

**How to apply:** Name each job and action a change adds with a verb first. Older jobs named otherwise, such as `clang-format` or `yamllint`, are left as they are unless the user asks.
