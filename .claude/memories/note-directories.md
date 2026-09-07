---
name: note-directories
description: The session notes live in this repository under .claude/memories/, a single flat directory since 2026-09-07.
metadata:
  type: feedback
---

# Where the notes live

Write the notes into this repository under `.claude/memories/`, rather than into the per-project directory beneath `~/.claude/projects/`.

**Why:** The user asked for the in-repository location on 2026-09-05. The directory is tracked in git, so a note written there travels with the repository and is readable by anyone working in it, while the path under `~/.claude/projects/` is local to one machine and empty.

**How to apply:** One flat directory, one fact per file — see [recording-what-a-session-learns](recording-what-a-session-learns.md) for the shape of a file.

The directory has been reorganised twice, which is why an older commit or note may name a path that no longer exists. On 2026-09-05 the notes were split four ways by kind, into `rules/`, `conventions/`, `memories/` and `references/`, with `.claude/CLAUDE.md` carrying a summary of each rule and convention; before that split everything but two files sat in `rules/`. An `incidents/` directory held recollections of single events for part of that day and was removed, the repository already carrying its own history in the log. On 2026-09-07 the user asked for the whole of it to be collapsed into `.claude/memories/`, and `CLAUDE.md`, `rules/`, `conventions/` and `references/` were deleted.

One consequence of that collapse is worth knowing. `CLAUDE.md` was injected into every session in full; `MEMORY.md` is, but the memory bodies arrive by relevance-based recall instead. So a rule with a CI gate behind it is no longer guaranteed to be in context, which is why the `MEMORY.md` index lines state their rules imperatively rather than merely naming them.
