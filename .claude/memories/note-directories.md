---
name: note-directories
description: The session notes live in this repository under .claude/memories/, a single flat directory.
metadata:
  type: feedback
---

# Where the notes live

Write the notes into this repository under `.claude/memories/`, rather than into the per-project directory beneath `~/.claude/projects/`.

**Why:** The directory is tracked in git, so a note written there travels with the repository and is readable by anyone working in it, while the path under `~/.claude/projects/` is local to one machine and empty.

**How to apply:** One flat directory, one fact per file — see [recording-what-a-session-learns](recording-what-a-session-learns.md) for the shape of a file.

`MEMORY.md` is loaded into every session in full, but the memory bodies arrive by relevance-based recall, so a rule, even one with a CI gate behind it, is not guaranteed to be in context. That is why the `MEMORY.md` index lines state their rules imperatively rather than merely naming them.
