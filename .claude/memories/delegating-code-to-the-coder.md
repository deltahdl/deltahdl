---
name: delegating-code-to-the-coder
description: The main session, on the latest Opus at high effort, researches and orchestrates; every code edit goes to the coder subagent, on the latest Sonnet at high effort.
metadata:
  type: feedback
---

# Delegating code to the coder

The main session researches, coordinates and orchestrates; it hands every change to `src/`, `test/`, `lib/python`, `scripts` and their tests to the `coder` subagent defined in `.claude/agents/coder.md`.

**Why:** The user wants the latest Opus at high effort for research, coordination and orchestration, and the latest Sonnet at high effort for writing code, whichever versions those are when the session runs. `.claude/settings.json` names the main session's model by the alias `opus` and the agent's front matter names the coder's by `sonnet`, never by a versioned ID, since an alias resolves to the newest release and an ID stays behind when the next one ships. Nothing in either makes a session delegate; this note does.

**How to apply:** The main session reads the issues and the clause of IEEE 1800-2023 ([[lrm-source-of-truth]]), settles the batch ([[grouping-issues-into-a-push]]), and gives the coder a brief that stands alone: the issues, the clause and what it requires, the files and tests in scope. Independent parts of a batch may go to several coders at once when they touch disjoint files. The main session then reviews the coder's diff against the clause, stages explicit paths ([[git-add-explicit-paths]]), commits, pushes and reads the run ([[verifying-through-ci]]). Fixing a red run is code too and goes to the coder with the failing log in the brief.
