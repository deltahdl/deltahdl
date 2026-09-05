---
name: note-directories
description: The session notes live in the repository under .claude/, split four ways by kind since 2026-09-05.
metadata:
  type: feedback
---

# Where the notes live

Write the notes into this repository under `.claude/`, rather than into the per-project directory beneath `~/.claude/projects/`. The user asked for this on 2026-09-05. Every one of these directories is tracked in git, so a note written there travels with the repository and is readable by anyone working in it, while the path under `~/.claude/projects/` is local to one machine and empty.

The same day, the notes were split by what each one is: `rules/` for an instruction with a gate or a mechanism behind it, `conventions/` for a chosen form that a different choice would serve as well, `memories/` for a standing fact the repository does not record on its own, and `references/` for lookup material. Before that split, everything but two files sat in `rules/`, which is why an older commit or note may name `.claude/rules/` for something now filed elsewhere.

An `incidents/` directory held recollections of single events for part of that day and was removed: the repository already carries its own history in the log, and a rule is followed from its instruction rather than from the story of the time it was broken.

The four kinds are defined in the Recording section of `.claude/CLAUDE.md`, which is what a session reads first.
